// Lean compiler output
// Module: Lean.Elab.Deriving.BEq
// Imports: public import Lean.Data.Options import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CasesOnSameCtor import Lean.Meta.SameCtorUtils import Init.Data.Array.OfFn
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 188, 150, 126, 202, 210, 87, 56)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(2, 35, 48, 234, 208, 30, 169, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for implementing `BEq` that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 165, 225, 156, 115, 202, 230, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(71, 221, 4, 81, 40, 1, 30, 26)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 242, 38, 149, 146, 119, 211, 138)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 78, 208, 242, 44, 150, 100, 230)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 129, 112, 189, 241, 241, 163, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 208, 129, 142, 173, 19, 33, 85)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(71, 160, 64, 149, 162, 78, 171, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 92, 31, 179, 36, 246, 140, 67)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 196, 248, 71, 32, 17, 147, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_&&_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 195, 203, 117, 177, 125, 57, 22)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_==_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(25, 251, 60, 160, 118, 54, 158, 27)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 26, 2, 19, 145, 121, 166, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_of_beq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value),LEAN_SCALAR_PTR_LITERAL(222, 43, 1, 254, 31, 20, 2, 112)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value),LEAN_SCALAR_PTR_LITERAL(55, 38, 224, 243, 7, 50, 169, 202)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Deriving.BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Elab.Deriving.BEq.0.Lean.Elab.Deriving.BEq.mkMatchNew"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: header.targetNames.size == 2\n\n  "};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "match_on_same_ctor"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 38, 237, 47, 106, 10, 11, 248)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Nat.decEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 20, 163, 238, 100, 115, 187, 44)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "match.ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value),LEAN_SCALAR_PTR_LITERAL(49, 254, 67, 85, 227, 127, 91, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 204, 183, 225, 123, 221, 75, 96)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "x.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(2, 247, 218, 116, 51, 159, 161, 152)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "y.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(85, 37, 232, 186, 208, 254, 208, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "method_specs"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(101, 159, 225, 215, 58, 146, 25, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 135, 164, 219, 193, 11, 15, 193)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 118, 133, 101, 222, 86, 142, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 129, 53, 81, 247, 98, 179, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 213, 169, 55, 145, 123, 160, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(71, 28, 210, 8, 101, 35, 72, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 53, 125, 167, 22, 113, 17, 93)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(993467269) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 184, 182, 130, 80, 10, 154, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 174, 45, 45, 68, 195, 231, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 45, 241, 81, 166, 228, 249, 231)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(98, 175, 82, 143, 146, 81, 47, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
lean_inc(v_defValue_5_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v_defValue_5_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_9_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_9_, 0, v_name_1_);
lean_ctor_set(v___x_9_, 1, v_ref_3_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v_descr_6_);
lean_ctor_set(v___x_9_, 4, v_deprecation_x3f_7_);
v___x_10_ = lean_register_option(v_name_1_, v___x_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 0);
lean_dec(v_unused_19_);
v___x_12_ = v___x_10_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_dec(v___x_10_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_defValue_5_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_name_1_);
lean_ctor_set(v___x_14_, 1, v_defValue_5_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_name_1_);
v_a_20_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_10_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_10_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_93_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v___x_90_, v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(lean_object* v_indVal_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_107_ = lean_unsigned_to_nat(2u);
v___x_108_ = l_Lean_Elab_Deriving_mkHeader(v___x_106_, v___x_107_, v_indVal_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___boxed(lean_object* v_indVal_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_ref_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_ref_125_ = lean_ctor_get(v___y_122_, 2);
v___x_126_ = 0;
v___x_127_ = l_Lean_SourceInfo_fromRef(v_ref_125_, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed(lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(lean_object* v_upperBound_146_, lean_object* v_a_147_, lean_object* v_b_148_, lean_object* v___y_149_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_lt(v_a_147_, v_upperBound_146_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_a_147_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v_b_148_);
return v___x_152_;
}
else
{
lean_object* v_ref_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_ref_153_ = lean_ctor_get(v___y_149_, 2);
v___x_154_ = 0;
v___x_155_ = l_Lean_SourceInfo_fromRef(v_ref_153_, v___x_154_);
v___x_156_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_157_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_155_);
v___x_158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_155_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_Syntax_node1(v___x_155_, v___x_156_, v___x_158_);
v___x_160_ = lean_array_push(v_b_148_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_a_147_, v___x_161_);
lean_dec(v_a_147_);
v_a_147_ = v___x_162_;
v_b_148_ = v___x_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___boxed(lean_object* v_upperBound_164_, lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_164_, v_a_165_, v_b_166_, v___y_167_);
lean_dec_ref(v___y_167_);
lean_dec(v_upperBound_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(size_t v_sz_170_, size_t v_i_171_, lean_object* v_bs_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_lt(v_i_171_, v_sz_170_);
if (v___x_173_ == 0)
{
return v_bs_172_;
}
else
{
lean_object* v_v_174_; lean_object* v___x_175_; lean_object* v_bs_x27_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v_v_174_ = lean_array_uget(v_bs_172_, v_i_171_);
v___x_175_ = lean_unsigned_to_nat(0u);
v_bs_x27_176_ = lean_array_uset(v_bs_172_, v_i_171_, v___x_175_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_171_, v___x_177_);
v___x_179_ = lean_array_uset(v_bs_x27_176_, v_i_171_, v_v_174_);
v_i_171_ = v___x_178_;
v_bs_172_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0___boxed(lean_object* v_sz_181_, lean_object* v_i_182_, lean_object* v_bs_183_){
_start:
{
size_t v_sz_boxed_184_; size_t v_i_boxed_185_; lean_object* v_res_186_; 
v_sz_boxed_184_ = lean_unbox_usize(v_sz_181_);
lean_dec(v_sz_181_);
v_i_boxed_185_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_boxed_184_, v_i_boxed_185_, v_bs_183_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1));
v___x_191_ = l_String_toRawSubstring_x27(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Array_mkArray0___redArg();
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14));
v___x_217_ = l_Lean_mkAtom(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(lean_object* v_indVal_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_numIndices_227_; lean_object* v___x_228_; lean_object* v_patterns_229_; lean_object* v___x_230_; 
v_numIndices_227_ = lean_ctor_get(v_indVal_219_, 2);
v___x_228_ = lean_unsigned_to_nat(0u);
v_patterns_229_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_227_, v___x_228_, v_patterns_229_, v_a_224_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_toCold_232_; lean_object* v_ref_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_a_243_; lean_object* v_quotContext_244_; lean_object* v_currMacroScope_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_275_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_toCold_232_ = lean_ctor_get(v_a_224_, 0);
v_ref_233_ = lean_ctor_get(v_a_224_, 2);
v___x_234_ = 0;
v___x_235_ = l_Lean_SourceInfo_fromRef(v_ref_233_, v___x_234_);
v___x_236_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_237_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_235_);
v___x_238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_Syntax_node1(v___x_235_, v___x_236_, v___x_238_);
lean_inc(v___x_239_);
v___x_240_ = lean_array_push(v_a_231_, v___x_239_);
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
v___x_242_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v___x_242_);
v_quotContext_244_ = lean_ctor_get(v_toCold_232_, 8);
v_currMacroScope_245_ = lean_ctor_get(v_toCold_232_, 9);
v___x_246_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
lean_inc(v_currMacroScope_245_);
lean_inc(v_quotContext_244_);
v___x_248_ = l_Lean_addMacroScope(v_quotContext_244_, v___x_247_, v_currMacroScope_245_);
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_250_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_250_, 0, v_a_243_);
lean_ctor_set(v___x_250_, 1, v___x_246_);
lean_ctor_set(v___x_250_, 2, v___x_248_);
lean_ctor_set(v___x_250_, 3, v___x_249_);
v___x_251_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_275_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_275_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_275_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc_n(v_a_252_, 4);
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v_a_252_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_260_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v_sz_261_ = lean_array_size(v___x_241_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_261_, v___x_262_, v___x_241_);
v___x_264_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_265_ = l_Lean_mkSepArray(v___x_263_, v___x_264_);
lean_dec_ref(v___x_263_);
v___x_266_ = l_Array_append___redArg(v___x_260_, v___x_265_);
lean_dec_ref(v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v_a_252_);
lean_ctor_set(v___x_267_, 1, v___x_259_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = l_Lean_Syntax_node1(v_a_252_, v___x_259_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_252_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_Syntax_node4(v_a_252_, v___x_256_, v___x_258_, v___x_268_, v___x_270_, v___x_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_271_);
v___x_273_ = v___x_254_;
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
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_230_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_230_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object* v_indVal_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_indVal_284_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object* v_upperBound_293_, lean_object* v_inst_294_, lean_object* v_R_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_c_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_293_, v_a_296_, v_b_297_, v___y_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object* v_upperBound_307_, lean_object* v_inst_308_, lean_object* v_R_309_, lean_object* v_a_310_, lean_object* v_b_311_, lean_object* v_c_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(v_upperBound_307_, v_inst_308_, v_R_309_, v_a_310_, v_b_311_, v_c_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v_upperBound_307_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v_b_324_, lean_object* v_c_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_331_ = lean_apply_9(v_k_321_, v_b_324_, v_c_325_, v___y_322_, v___y_323_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v_b_335_, lean_object* v_c_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(v_k_332_, v___y_333_, v___y_334_, v_b_335_, v_c_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_type_343_, lean_object* v_k_344_, uint8_t v_cleanupAnnotations_345_, uint8_t v_whnfType_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; 
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_354_, 0, v_k_344_);
lean_closure_set(v___f_354_, 1, v___y_347_);
lean_closure_set(v___f_354_, 2, v___y_348_);
v___x_355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_343_, v___f_354_, v_cleanupAnnotations_345_, v_whnfType_346_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_355_) == 0)
{
return v___x_355_;
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_type_364_, lean_object* v_k_365_, lean_object* v_cleanupAnnotations_366_, lean_object* v_whnfType_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_375_; uint8_t v_whnfType_boxed_376_; lean_object* v_res_377_; 
v_cleanupAnnotations_boxed_375_ = lean_unbox(v_cleanupAnnotations_366_);
v_whnfType_boxed_376_ = lean_unbox(v_whnfType_367_);
v_res_377_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_364_, v_k_365_, v_cleanupAnnotations_boxed_375_, v_whnfType_boxed_376_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object* v_00_u03b1_378_, lean_object* v_type_379_, lean_object* v_k_380_, uint8_t v_cleanupAnnotations_381_, uint8_t v_whnfType_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_379_, v_k_380_, v_cleanupAnnotations_381_, v_whnfType_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_391_, lean_object* v_type_392_, lean_object* v_k_393_, lean_object* v_cleanupAnnotations_394_, lean_object* v_whnfType_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_403_; uint8_t v_whnfType_boxed_404_; lean_object* v_res_405_; 
v_cleanupAnnotations_boxed_403_ = lean_unbox(v_cleanupAnnotations_394_);
v_whnfType_boxed_404_ = lean_unbox(v_whnfType_395_);
v_res_405_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(v_00_u03b1_391_, v_type_392_, v_k_393_, v_cleanupAnnotations_boxed_403_, v_whnfType_boxed_404_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v___x_406_, lean_object* v_as_407_, size_t v_i_408_, size_t v_stop_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = lean_usize_dec_eq(v_i_408_, v_stop_409_);
if (v___x_415_ == 0)
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = 1;
v___x_417_ = lean_array_uget_borrowed(v_as_407_, v_i_408_);
lean_inc(v___y_413_);
lean_inc_ref(v___y_412_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___x_417_);
v___x_418_ = lean_infer_type(v___x_417_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_432_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_432_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_432_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_432_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = l_Lean_Expr_fvarId_x21(v___x_406_);
v___x_424_ = l_Lean_Expr_containsFVar(v_a_419_, v___x_423_);
lean_dec(v___x_423_);
lean_dec(v_a_419_);
if (v___x_424_ == 0)
{
size_t v___x_425_; size_t v___x_426_; 
lean_del_object(v___x_421_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_408_, v___x_425_);
v_i_408_ = v___x_426_;
goto _start;
}
else
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_box(v___x_416_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_428_);
v___x_430_ = v___x_421_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_418_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_418_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v___x_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
size_t v_i_boxed_453_; size_t v_stop_boxed_454_; lean_object* v_res_455_; 
v_i_boxed_453_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_454_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_444_, v_as_445_, v_i_boxed_453_, v_stop_boxed_454_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v_as_445_);
lean_dec_ref(v___x_444_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_ref_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_ref_463_ = lean_ctor_get(v___y_460_, 2);
v___x_464_ = 0;
v___x_465_ = l_Lean_SourceInfo_fromRef(v_ref_463_, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_474_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15));
v___x_499_ = l_String_toRawSubstring_x27(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_554_ = l_String_toRawSubstring_x27(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53));
v___x_591_ = l_String_toRawSubstring_x27(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_625_, lean_object* v_indVal_626_, lean_object* v___x_627_, lean_object* v_xs_628_, lean_object* v_a_629_, lean_object* v_auxFunName_630_, lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_a_641_; uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_lt(v_a_631_, v_upperBound_625_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_b_632_);
return v___x_646_;
}
else
{
lean_object* v_snd_647_; lean_object* v_snd_648_; lean_object* v_fst_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_991_; 
v_snd_647_ = lean_ctor_get(v_b_632_, 1);
lean_inc(v_snd_647_);
v_snd_648_ = lean_ctor_get(v_snd_647_, 1);
lean_inc(v_snd_648_);
v_fst_649_ = lean_ctor_get(v_b_632_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_b_632_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_b_632_, 1);
lean_dec(v_unused_992_);
v___x_651_ = v_b_632_;
v_isShared_652_ = v_isSharedCheck_991_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_fst_649_);
lean_dec(v_b_632_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_991_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_fst_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_989_; 
v_fst_653_ = lean_ctor_get(v_snd_647_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_snd_647_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_snd_647_, 1);
lean_dec(v_unused_990_);
v___x_655_ = v_snd_647_;
v_isShared_656_ = v_isSharedCheck_989_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_fst_653_);
lean_dec(v_snd_647_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_989_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_988_; 
v_fst_657_ = lean_ctor_get(v_snd_648_, 0);
v_snd_658_ = lean_ctor_get(v_snd_648_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_snd_648_);
if (v_isSharedCheck_988_ == 0)
{
v___x_660_ = v_snd_648_;
v_isShared_661_ = v_isSharedCheck_988_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v_snd_648_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_988_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_toConstantVal_662_; lean_object* v_numParams_663_; lean_object* v_lctx_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_toConstantVal_662_ = lean_ctor_get(v_indVal_626_, 0);
lean_inc_ref(v_toConstantVal_662_);
v_numParams_663_ = lean_ctor_get(v_indVal_626_, 1);
v_lctx_664_ = lean_ctor_get(v___y_635_, 2);
v___x_665_ = l_Lean_instInhabitedExpr;
v___x_666_ = lean_nat_add(v_numParams_663_, v___x_627_);
v___x_667_ = lean_nat_sub(v___x_666_, v_a_631_);
lean_dec(v___x_666_);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_sub(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_array_get_borrowed(v___x_665_, v_xs_628_, v___x_669_);
lean_inc(v___x_670_);
lean_inc_ref(v_lctx_664_);
v___x_671_ = l_Lean_Meta_occursOrInType(v_lctx_664_, v___x_670_, v_a_629_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_673_ = l_Lean_Core_mkFreshUserName(v___x_672_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = l_Lean_mkIdent(v_a_674_);
v___x_676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3));
v___x_677_ = l_Lean_Core_mkFreshUserName(v___x_676_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v_a_683_; lean_object* v___x_736_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = l_Lean_mkIdent(v_a_678_);
lean_inc(v___x_675_);
v___x_680_ = lean_array_push(v_fst_649_, v___x_675_);
lean_inc(v___x_679_);
v___x_681_ = lean_array_push(v_fst_653_, v___x_679_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___x_670_);
v___x_736_ = lean_infer_type(v___x_670_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc_n(v_a_737_, 2);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_Meta_isProp(v_a_737_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_unbox(v_a_739_);
if (v___x_740_ == 0)
{
lean_object* v_name_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_911_; 
v_name_741_ = lean_ctor_get(v_toConstantVal_662_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_toConstantVal_662_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_912_ = lean_ctor_get(v_toConstantVal_662_, 2);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_toConstantVal_662_, 1);
lean_dec(v_unused_913_);
v___x_743_ = v_toConstantVal_662_;
v_isShared_744_ = v_isSharedCheck_911_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_name_741_);
lean_dec(v_toConstantVal_662_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_911_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v_lower_857_; lean_object* v_upper_858_; 
v___x_745_ = l_Lean_Expr_isAppOf(v_a_737_, v_name_741_);
lean_dec(v_name_741_);
lean_dec(v_a_737_);
if (v___x_745_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
lean_dec(v_a_739_);
v___x_866_ = lean_nat_add(v___x_669_, v___x_668_);
lean_dec(v___x_669_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_xs_628_);
v___x_869_ = lean_nat_dec_le(v___x_866_, v___x_867_);
if (v___x_869_ == 0)
{
v_lower_857_ = v___x_866_;
v_upper_858_ = v___x_868_;
goto v___jp_856_;
}
else
{
lean_dec(v___x_866_);
v_lower_857_ = v___x_867_;
v_upper_858_ = v___x_868_;
goto v___jp_856_;
}
}
else
{
uint8_t v___x_870_; 
lean_del_object(v___x_743_);
lean_dec(v___x_669_);
lean_del_object(v___x_660_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
v___x_870_ = lean_unbox(v_snd_658_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_a_739_);
v___x_871_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc_n(v_a_872_, 4);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_630_);
v___x_875_ = l_Lean_mkIdent(v_auxFunName_630_);
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_877_ = l_Lean_Syntax_node2(v_a_872_, v___x_876_, v___x_675_, v___x_679_);
v___x_878_ = l_Lean_Syntax_node2(v_a_872_, v___x_874_, v___x_875_, v___x_877_);
v___x_879_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v_a_872_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Syntax_node3(v_a_872_, v___x_873_, v___x_878_, v___x_880_, v_fst_657_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_snd_658_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_681_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_680_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v_a_641_ = v___x_884_;
goto v___jp_640_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_885_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_871_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_871_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
v___x_893_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_n(v_a_894_, 2);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_630_);
v___x_896_ = l_Lean_mkIdent(v_auxFunName_630_);
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_898_ = l_Lean_Syntax_node2(v_a_894_, v___x_897_, v___x_675_, v___x_679_);
v___x_899_ = l_Lean_Syntax_node2(v_a_894_, v___x_895_, v___x_896_, v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_a_739_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_681_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_680_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v_a_641_ = v___x_902_;
goto v___jp_640_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_739_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_903_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_893_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
v___jp_746_:
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_lt(v___y_747_, v___y_749_);
if (v___x_750_ == 0)
{
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_del_object(v___x_743_);
v_a_683_ = v___x_750_;
goto v___jp_682_;
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_usize_of_nat(v___y_747_);
lean_dec(v___y_747_);
v___x_752_ = lean_usize_of_nat(v___y_749_);
lean_dec(v___y_749_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_670_, v___y_748_, v___x_751_, v___x_752_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v___y_748_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; uint8_t v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = lean_unbox(v_a_754_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; 
lean_del_object(v___x_743_);
v___x_756_ = lean_unbox(v_a_754_);
lean_dec(v_a_754_);
v_a_683_ = v___x_756_;
goto v___jp_682_;
}
else
{
lean_object* v___x_757_; 
lean_dec(v_a_754_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
v___x_757_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_toCold_758_; lean_object* v_a_759_; lean_object* v_quotContext_760_; lean_object* v_currMacroScope_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_toCold_758_ = lean_ctor_get(v___y_637_, 0);
v_a_759_ = lean_ctor_get(v___x_757_, 0);
lean_inc_n(v_a_759_, 11);
lean_dec_ref_known(v___x_757_, 1);
v_quotContext_760_ = lean_ctor_get(v_toCold_758_, 8);
v_currMacroScope_761_ = lean_ctor_get(v_toCold_758_, 9);
v___x_762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v_a_759_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc(v_currMacroScope_761_);
lean_inc(v_quotContext_760_);
v___x_768_ = l_Lean_addMacroScope(v_quotContext_760_, v___x_767_, v_currMacroScope_761_);
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_770_, 0, v_a_759_);
lean_ctor_set(v___x_770_, 1, v___x_766_);
lean_ctor_set(v___x_770_, 2, v___x_768_);
lean_ctor_set(v___x_770_, 3, v___x_769_);
lean_inc_ref(v___x_770_);
v___x_771_ = l_Lean_Syntax_node1(v_a_759_, v___x_765_, v___x_770_);
v___x_772_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v_a_759_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_775_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v_a_759_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Syntax_node3(v_a_759_, v___x_774_, v___x_675_, v___x_776_, v___x_679_);
v___x_778_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_779_, 0, v_a_759_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_759_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_784_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_759_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
v___x_789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_790_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
lean_ctor_set(v___x_743_, 2, v___x_790_);
lean_ctor_set(v___x_743_, 1, v___x_785_);
lean_ctor_set(v___x_743_, 0, v_a_759_);
v___x_792_ = v___x_743_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_839_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_794_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v_a_759_, 20);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v_a_759_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_798_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_799_ = lean_box(0);
lean_inc_n(v_currMacroScope_761_, 3);
lean_inc_n(v_quotContext_760_, 3);
v___x_800_ = l_Lean_addMacroScope(v_quotContext_760_, v___x_799_, v_currMacroScope_761_);
v___x_801_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_802_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_802_, 0, v_a_759_);
lean_ctor_set(v___x_802_, 1, v___x_798_);
lean_ctor_set(v___x_802_, 2, v___x_800_);
lean_ctor_set(v___x_802_, 3, v___x_801_);
v___x_803_ = l_Lean_Syntax_node1(v_a_759_, v___x_797_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node2(v_a_759_, v___x_794_, v___x_796_, v___x_803_);
v___x_805_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_806_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_807_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_808_ = l_Lean_addMacroScope(v_quotContext_760_, v___x_807_, v_currMacroScope_761_);
v___x_809_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_810_, 0, v_a_759_);
lean_ctor_set(v___x_810_, 1, v___x_806_);
lean_ctor_set(v___x_810_, 2, v___x_808_);
lean_ctor_set(v___x_810_, 3, v___x_809_);
v___x_811_ = l_Lean_Syntax_node1(v_a_759_, v___x_785_, v___x_770_);
v___x_812_ = l_Lean_Syntax_node2(v_a_759_, v___x_805_, v___x_810_, v___x_811_);
v___x_813_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_759_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_Syntax_node3(v_a_759_, v___x_793_, v___x_804_, v___x_812_, v___x_814_);
lean_inc_ref_n(v___x_792_, 3);
v___x_816_ = l_Lean_Syntax_node2(v_a_759_, v___x_789_, v___x_792_, v___x_815_);
v___x_817_ = l_Lean_Syntax_node1(v_a_759_, v___x_785_, v___x_816_);
v___x_818_ = l_Lean_Syntax_node4(v_a_759_, v___x_787_, v___x_788_, v___x_817_, v___x_792_, v___x_792_);
v___x_819_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_820_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_759_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
v___x_822_ = l_Lean_Syntax_node2(v_a_759_, v___x_820_, v___x_821_, v_fst_657_);
v___x_823_ = l_Lean_Syntax_node3(v_a_759_, v___x_785_, v___x_818_, v___x_792_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node1(v_a_759_, v___x_784_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node1(v_a_759_, v___x_783_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node2(v_a_759_, v___x_780_, v___x_782_, v___x_825_);
v___x_827_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_759_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_831_ = l_Lean_addMacroScope(v_quotContext_760_, v___x_830_, v_currMacroScope_761_);
v___x_832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_833_, 0, v_a_759_);
lean_ctor_set(v___x_833_, 1, v___x_829_);
lean_ctor_set(v___x_833_, 2, v___x_831_);
lean_ctor_set(v___x_833_, 3, v___x_832_);
v___x_834_ = l_Lean_Syntax_node8(v_a_759_, v___x_762_, v___x_764_, v___x_771_, v___x_773_, v___x_777_, v___x_779_, v___x_826_, v___x_828_, v___x_833_);
v___x_835_ = lean_box(v___x_745_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_681_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_680_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v_a_641_ = v___x_838_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_743_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v_fst_657_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_840_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_757_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_757_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_743_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_848_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_753_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_753_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
v___jp_856_:
{
lean_object* v___x_859_; lean_object* v_array_860_; lean_object* v_start_861_; lean_object* v_stop_862_; uint8_t v___x_863_; 
lean_inc_ref(v_xs_628_);
v___x_859_ = l_Array_toSubarray___redArg(v_xs_628_, v_lower_857_, v_upper_858_);
v_array_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_array_860_);
v_start_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_start_861_);
v_stop_862_ = lean_ctor_get(v___x_859_, 2);
lean_inc(v_stop_862_);
lean_dec_ref(v___x_859_);
v___x_863_ = lean_nat_dec_lt(v_start_861_, v_stop_862_);
if (v___x_863_ == 0)
{
lean_dec(v_stop_862_);
lean_dec(v_start_861_);
lean_dec_ref(v_array_860_);
lean_del_object(v___x_743_);
v_a_683_ = v___x_863_;
goto v___jp_682_;
}
else
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_array_get_size(v_array_860_);
v___x_865_ = lean_nat_dec_le(v_stop_862_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec(v_stop_862_);
v___y_747_ = v_start_861_;
v___y_748_ = v_array_860_;
v___y_749_ = v___x_864_;
goto v___jp_746_;
}
else
{
v___y_747_ = v_start_861_;
v___y_748_ = v_array_860_;
v___y_749_ = v_stop_862_;
goto v___jp_746_;
}
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec(v_a_739_);
lean_dec(v_a_737_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
lean_del_object(v___x_660_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_fst_657_);
lean_ctor_set(v___x_914_, 1, v_snd_658_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_681_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_680_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v_a_641_ = v___x_916_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_737_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_917_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_738_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_738_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_925_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_736_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_736_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
v___jp_682_:
{
uint8_t v___x_684_; 
v___x_684_ = lean_unbox(v_snd_658_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_n(v_a_686_, 4);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v_a_686_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_Syntax_node3(v_a_686_, v___x_688_, v___x_675_, v___x_690_, v___x_679_);
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_686_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Syntax_node3(v_a_686_, v___x_687_, v___x_691_, v___x_693_, v_fst_657_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_694_);
v___x_696_ = v___x_660_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_658_);
v___x_696_ = v_reuseFailAlloc_703_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_696_);
lean_ctor_set(v___x_655_, 0, v___x_681_);
v___x_698_ = v___x_655_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_698_);
lean_ctor_set(v___x_651_, 0, v___x_680_);
v___x_700_ = v___x_651_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v_a_641_ = v___x_700_;
goto v___jp_640_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_704_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_685_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_685_);
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
else
{
lean_object* v___x_712_; 
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
v___x_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_n(v_a_713_, 2);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v_a_713_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_Syntax_node3(v_a_713_, v___x_714_, v___x_675_, v___x_716_, v___x_679_);
v___x_718_ = lean_box(v_a_683_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_718_);
lean_ctor_set(v___x_660_, 0, v___x_717_);
v___x_720_ = v___x_660_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_727_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_720_);
lean_ctor_set(v___x_655_, 0, v___x_681_);
v___x_722_ = v___x_655_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_722_);
lean_ctor_set(v___x_651_, 0, v___x_680_);
v___x_724_ = v___x_651_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v_a_641_ = v___x_724_;
goto v___jp_640_;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
lean_dec(v___x_675_);
lean_del_object(v___x_660_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_728_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_712_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_712_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
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
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v___x_675_);
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_dec(v_fst_653_);
lean_del_object(v___x_651_);
lean_dec(v_fst_649_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_933_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_677_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_677_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_dec(v_fst_653_);
lean_del_object(v___x_651_);
lean_dec(v_fst_649_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_941_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_673_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_673_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v___x_669_);
lean_dec_ref(v_toConstantVal_662_);
v___x_949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_950_ = l_Lean_Core_mkFreshUserName(v___x_949_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = l_Lean_mkIdent(v_a_951_);
lean_inc(v___x_952_);
v___x_953_ = lean_array_push(v_fst_649_, v___x_952_);
v___x_954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_n(v_a_955_, 3);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67));
v___x_957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68));
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v_a_955_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v_a_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_Syntax_node3(v_a_955_, v___x_956_, v___x_958_, v___x_952_, v___x_960_);
v___x_962_ = lean_array_push(v_fst_653_, v___x_961_);
if (v_isShared_661_ == 0)
{
v___x_964_ = v___x_660_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_snd_658_);
v___x_964_ = v_reuseFailAlloc_971_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_964_);
lean_ctor_set(v___x_655_, 0, v___x_962_);
v___x_966_ = v___x_655_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_966_);
lean_ctor_set(v___x_651_, 0, v___x_953_);
v___x_968_ = v___x_651_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_a_641_ = v___x_968_;
goto v___jp_640_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___x_953_);
lean_dec(v___x_952_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_dec(v_fst_653_);
lean_del_object(v___x_651_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_972_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_954_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_954_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_dec(v_fst_653_);
lean_del_object(v___x_651_);
lean_dec(v_fst_649_);
lean_dec(v_a_631_);
lean_dec(v_auxFunName_630_);
lean_dec_ref(v_xs_628_);
lean_dec_ref(v_indVal_626_);
v_a_980_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_950_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_950_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
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
}
}
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_a_631_, v___x_642_);
lean_dec(v_a_631_);
v_a_631_ = v___x_643_;
v_b_632_ = v_a_641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_993_, lean_object* v_indVal_994_, lean_object* v___x_995_, lean_object* v_xs_996_, lean_object* v_a_997_, lean_object* v_auxFunName_998_, lean_object* v_a_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_993_, v_indVal_994_, v___x_995_, v_xs_996_, v_a_997_, v_auxFunName_998_, v_a_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_a_997_);
lean_dec(v___x_995_);
lean_dec(v_upperBound_993_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object* v_upperBound_1009_, lean_object* v_a_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_lt(v_a_1010_, v_upperBound_1009_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec(v_a_1010_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1011_);
return v___x_1020_;
}
else
{
lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1060_; 
v_fst_1021_ = lean_ctor_get(v_b_1011_, 0);
v_snd_1022_ = lean_ctor_get(v_b_1011_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_b_1011_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1024_ = v_b_1011_;
v_isShared_1025_ = v_isSharedCheck_1060_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v_b_1011_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1060_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc_n(v_a_1027_, 2);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_1029_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_1030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_a_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node1(v_a_1027_, v___x_1028_, v___x_1030_);
v___x_1032_ = lean_array_push(v_fst_1021_, v___x_1031_);
v___x_1033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_n(v_a_1034_, 2);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1029_);
v___x_1036_ = l_Lean_Syntax_node1(v_a_1034_, v___x_1028_, v___x_1035_);
v___x_1037_ = lean_array_push(v_snd_1022_, v___x_1036_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1037_);
lean_ctor_set(v___x_1024_, 0, v___x_1032_);
v___x_1039_ = v___x_1024_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_add(v_a_1010_, v___x_1040_);
lean_dec(v_a_1010_);
v_a_1010_ = v___x_1041_;
v_b_1011_ = v___x_1039_;
goto _start;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___x_1032_);
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
lean_dec(v_a_1010_);
v_a_1044_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1033_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1033_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec(v_a_1010_);
v_a_1052_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1026_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1026_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1061_, v_a_1062_, v_b_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v_upperBound_1061_);
return v_res_1071_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_1074_ = l_String_toRawSubstring_x27(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object* v_indVal_1093_, lean_object* v___x_1094_, lean_object* v_alts_1095_, lean_object* v_numFields_1096_, lean_object* v_auxFunName_1097_, lean_object* v___f_1098_, lean_object* v_head_1099_, lean_object* v_xs_1100_, lean_object* v_type_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Core_betaReduce(v_type_1101_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_numParams_1111_; lean_object* v_numIndices_1112_; lean_object* v___x_1113_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v_numParams_1111_ = lean_ctor_get(v_indVal_1093_, 1);
lean_inc(v_numParams_1111_);
v_numIndices_1112_ = lean_ctor_get(v_indVal_1093_, 2);
lean_inc_ref(v_alts_1095_);
lean_inc(v___x_1094_);
v___x_1113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_1112_, v___x_1094_, v_alts_1095_, v___y_1106_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_toCold_1114_; lean_object* v_a_1115_; lean_object* v_ref_1116_; lean_object* v_quotContext_1117_; lean_object* v_currMacroScope_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_toCold_1114_ = lean_ctor_get(v___y_1106_, 0);
v_a_1115_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1113_, 1);
v_ref_1116_ = lean_ctor_get(v___y_1106_, 2);
v_quotContext_1117_ = lean_ctor_get(v_toCold_1114_, 8);
v_currMacroScope_1118_ = lean_ctor_get(v_toCold_1114_, 9);
v___x_1119_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_1120_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_1121_ = 0;
v___x_1122_ = l_Lean_SourceInfo_fromRef(v_ref_1116_, v___x_1121_);
lean_inc(v_currMacroScope_1118_);
lean_inc(v_quotContext_1117_);
v___x_1123_ = l_Lean_addMacroScope(v_quotContext_1117_, v___x_1120_, v_currMacroScope_1118_);
v___x_1124_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_1125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1122_);
lean_ctor_set(v___x_1125_, 1, v___x_1119_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
v___x_1126_ = 1;
v___x_1127_ = lean_box(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1125_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
lean_inc_ref(v_alts_1095_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_alts_1095_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_alts_1095_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_inc(v___x_1094_);
v___x_1131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_numFields_1096_, v_indVal_1093_, v_numFields_1096_, v_xs_1100_, v_a_1110_, v_auxFunName_1097_, v___x_1094_, v___x_1130_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v_a_1110_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_snd_1133_; lean_object* v_snd_1134_; lean_object* v_fst_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1247_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v_snd_1133_ = lean_ctor_get(v_a_1132_, 1);
lean_inc(v_snd_1133_);
v_snd_1134_ = lean_ctor_get(v_snd_1133_, 1);
lean_inc(v_snd_1134_);
v_fst_1135_ = lean_ctor_get(v_a_1132_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_a_1132_, 1);
lean_dec(v_unused_1248_);
v___x_1137_ = v_a_1132_;
v_isShared_1138_ = v_isSharedCheck_1247_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_fst_1135_);
lean_dec(v_a_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1247_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_fst_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1245_; 
v_fst_1139_ = lean_ctor_get(v_snd_1133_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_snd_1133_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_snd_1133_, 1);
lean_dec(v_unused_1246_);
v___x_1141_ = v_snd_1133_;
v_isShared_1142_ = v_isSharedCheck_1245_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_fst_1139_);
lean_dec(v_snd_1133_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1245_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_fst_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1243_; 
v_fst_1143_ = lean_ctor_get(v_snd_1134_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_snd_1134_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_snd_1134_, 1);
lean_dec(v_unused_1244_);
v___x_1145_ = v_snd_1134_;
v_isShared_1146_ = v_isSharedCheck_1243_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_fst_1143_);
lean_dec(v_snd_1134_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1243_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_fst_1139_);
lean_ctor_set(v___x_1145_, 0, v_fst_1135_);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_fst_1139_);
v___x_1148_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_numParams_1111_, v___x_1094_, v___x_1148_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v_numParams_1111_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1233_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v_fst_1151_ = lean_ctor_get(v_a_1150_, 0);
v_snd_1152_ = lean_ctor_get(v_a_1150_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_a_1150_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1154_ = v_a_1150_;
v_isShared_1155_ = v_isSharedCheck_1233_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_a_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1233_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; 
lean_inc_ref(v___f_1098_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
v___x_1156_ = lean_apply_7(v___f_1098_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc_n(v_a_1157_, 2);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_1159_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7));
v___x_1160_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 2);
lean_ctor_set(v___x_1154_, 1, v___x_1160_);
lean_ctor_set(v___x_1154_, 0, v_a_1157_);
v___x_1162_ = v___x_1154_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1163_ = l_Lean_mkIdent(v_head_1099_);
lean_inc(v___x_1163_);
lean_inc_n(v_a_1157_, 2);
v___x_1164_ = l_Lean_Syntax_node2(v_a_1157_, v___x_1159_, v___x_1162_, v___x_1163_);
v___x_1165_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1166_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1167_ = l_Array_reverse___redArg(v_fst_1151_);
v___x_1168_ = l_Array_append___redArg(v___x_1166_, v___x_1167_);
lean_dec_ref(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1169_, 0, v_a_1157_);
lean_ctor_set(v___x_1169_, 1, v___x_1165_);
lean_ctor_set(v___x_1169_, 2, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node2(v_a_1157_, v___x_1158_, v___x_1164_, v___x_1169_);
v___x_1171_ = lean_array_push(v_a_1115_, v___x_1170_);
lean_inc_ref(v___f_1098_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
v___x_1172_ = lean_apply_7(v___f_1098_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_n(v_a_1173_, 2);
lean_dec_ref_known(v___x_1172_, 1);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 2);
lean_ctor_set(v___x_1141_, 1, v___x_1160_);
lean_ctor_set(v___x_1141_, 0, v_a_1173_);
v___x_1175_ = v___x_1141_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1160_);
v___x_1175_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_inc_n(v_a_1173_, 2);
v___x_1176_ = l_Lean_Syntax_node2(v_a_1173_, v___x_1159_, v___x_1175_, v___x_1163_);
v___x_1177_ = l_Array_reverse___redArg(v_snd_1152_);
v___x_1178_ = l_Array_append___redArg(v___x_1166_, v___x_1177_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1179_, 0, v_a_1173_);
lean_ctor_set(v___x_1179_, 1, v___x_1165_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = l_Lean_Syntax_node2(v_a_1173_, v___x_1158_, v___x_1176_, v___x_1179_);
v___x_1181_ = lean_array_push(v___x_1171_, v___x_1180_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
v___x_1182_ = lean_apply_7(v___f_1098_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1206_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_1188_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc(v_a_1183_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 2);
lean_ctor_set(v___x_1137_, 1, v___x_1188_);
lean_ctor_set(v___x_1137_, 0, v_a_1183_);
v___x_1190_ = v___x_1137_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1183_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_sz_1191_ = lean_array_size(v___x_1181_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1191_, v___x_1192_, v___x_1181_);
v___x_1194_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1195_ = l_Lean_mkSepArray(v___x_1193_, v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_1196_ = l_Array_append___redArg(v___x_1166_, v___x_1195_);
lean_dec_ref(v___x_1195_);
lean_inc_n(v_a_1183_, 3);
v___x_1197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1183_);
lean_ctor_set(v___x_1197_, 1, v___x_1165_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_node1(v_a_1183_, v___x_1165_, v___x_1197_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_a_1183_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node4(v_a_1183_, v___x_1187_, v___x_1190_, v___x_1198_, v___x_1200_, v_fst_1143_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1201_);
v___x_1203_ = v___x_1185_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___x_1181_);
lean_dec(v_fst_1143_);
lean_del_object(v___x_1137_);
v_a_1207_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1182_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1182_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___x_1171_);
lean_dec(v___x_1163_);
lean_dec(v_snd_1152_);
lean_dec(v_fst_1143_);
lean_del_object(v___x_1141_);
lean_del_object(v___x_1137_);
lean_dec_ref(v___f_1098_);
v_a_1216_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1172_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1172_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_del_object(v___x_1154_);
lean_dec(v_snd_1152_);
lean_dec(v_fst_1151_);
lean_dec(v_fst_1143_);
lean_del_object(v___x_1141_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1115_);
lean_dec(v_head_1099_);
lean_dec_ref(v___f_1098_);
v_a_1225_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1156_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1156_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_fst_1143_);
lean_del_object(v___x_1141_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1115_);
lean_dec(v_head_1099_);
lean_dec_ref(v___f_1098_);
v_a_1234_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1149_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1149_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
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
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1115_);
lean_dec(v_numParams_1111_);
lean_dec(v_head_1099_);
lean_dec_ref(v___f_1098_);
lean_dec(v___x_1094_);
v_a_1249_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1131_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1131_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_numParams_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_xs_1100_);
lean_dec(v_head_1099_);
lean_dec_ref(v___f_1098_);
lean_dec(v_auxFunName_1097_);
lean_dec_ref(v_alts_1095_);
lean_dec(v___x_1094_);
lean_dec_ref(v_indVal_1093_);
v_a_1257_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1113_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1113_);
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
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_xs_1100_);
lean_dec(v_head_1099_);
lean_dec_ref(v___f_1098_);
lean_dec(v_auxFunName_1097_);
lean_dec_ref(v_alts_1095_);
lean_dec(v___x_1094_);
lean_dec_ref(v_indVal_1093_);
v_a_1265_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1109_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1109_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object* v_indVal_1273_, lean_object* v___x_1274_, lean_object* v_alts_1275_, lean_object* v_numFields_1276_, lean_object* v_auxFunName_1277_, lean_object* v___f_1278_, lean_object* v_head_1279_, lean_object* v_xs_1280_, lean_object* v_type_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(v_indVal_1273_, v___x_1274_, v_alts_1275_, v_numFields_1276_, v_auxFunName_1277_, v___f_1278_, v_head_1279_, v_xs_1280_, v_type_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v_numFields_1276_);
return v_res_1289_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_instMonadEIO___redArg();
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_toApplicative_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1398_; 
v___x_1305_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_1306_ = l_StateRefT_x27_instMonad___redArg(v___x_1305_);
v_toApplicative_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1306_, 1);
lean_dec(v_unused_1399_);
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1398_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_toApplicative_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1398_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_toFunctor_1311_; lean_object* v_toSeq_1312_; lean_object* v_toSeqLeft_1313_; lean_object* v_toSeqRight_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1396_; 
v_toFunctor_1311_ = lean_ctor_get(v_toApplicative_1307_, 0);
v_toSeq_1312_ = lean_ctor_get(v_toApplicative_1307_, 2);
v_toSeqLeft_1313_ = lean_ctor_get(v_toApplicative_1307_, 3);
v_toSeqRight_1314_ = lean_ctor_get(v_toApplicative_1307_, 4);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_toApplicative_1307_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v_toApplicative_1307_, 1);
lean_dec(v_unused_1397_);
v___x_1316_ = v_toApplicative_1307_;
v_isShared_1317_ = v_isSharedCheck_1396_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_toSeqRight_1314_);
lean_inc(v_toSeqLeft_1313_);
lean_inc(v_toSeq_1312_);
lean_inc(v_toFunctor_1311_);
lean_dec(v_toApplicative_1307_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1396_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___x_1327_; 
v___f_1318_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_1319_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1311_);
v___f_1320_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1320_, 0, v_toFunctor_1311_);
v___f_1321_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1321_, 0, v_toFunctor_1311_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___f_1320_);
lean_ctor_set(v___x_1322_, 1, v___f_1321_);
v___f_1323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1323_, 0, v_toSeqRight_1314_);
v___f_1324_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1324_, 0, v_toSeqLeft_1313_);
v___f_1325_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1325_, 0, v_toSeq_1312_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___f_1323_);
lean_ctor_set(v___x_1316_, 3, v___f_1324_);
lean_ctor_set(v___x_1316_, 2, v___f_1325_);
lean_ctor_set(v___x_1316_, 1, v___f_1318_);
lean_ctor_set(v___x_1316_, 0, v___x_1322_);
v___x_1327_ = v___x_1316_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___f_1318_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v___f_1325_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v___f_1324_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v___f_1323_);
v___x_1327_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___f_1319_);
lean_ctor_set(v___x_1309_, 0, v___x_1327_);
v___x_1329_ = v___x_1309_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___f_1319_);
v___x_1329_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v_toApplicative_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1392_; 
v___x_1330_ = l_StateRefT_x27_instMonad___redArg(v___x_1329_);
v_toApplicative_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1330_, 1);
lean_dec(v_unused_1393_);
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1392_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_toApplicative_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1392_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_toFunctor_1335_; lean_object* v_toSeq_1336_; lean_object* v_toSeqLeft_1337_; lean_object* v_toSeqRight_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1390_; 
v_toFunctor_1335_ = lean_ctor_get(v_toApplicative_1331_, 0);
v_toSeq_1336_ = lean_ctor_get(v_toApplicative_1331_, 2);
v_toSeqLeft_1337_ = lean_ctor_get(v_toApplicative_1331_, 3);
v_toSeqRight_1338_ = lean_ctor_get(v_toApplicative_1331_, 4);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_toApplicative_1331_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v_toApplicative_1331_, 1);
lean_dec(v_unused_1391_);
v___x_1340_ = v_toApplicative_1331_;
v_isShared_1341_ = v_isSharedCheck_1390_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_toSeqRight_1338_);
lean_inc(v_toSeqLeft_1337_);
lean_inc(v_toSeq_1336_);
lean_inc(v_toFunctor_1335_);
lean_dec(v_toApplicative_1331_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1390_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___f_1348_; lean_object* v___f_1349_; lean_object* v___x_1351_; 
v___f_1342_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1343_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1335_);
v___f_1344_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1344_, 0, v_toFunctor_1335_);
v___f_1345_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1345_, 0, v_toFunctor_1335_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___f_1344_);
lean_ctor_set(v___x_1346_, 1, v___f_1345_);
v___f_1347_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1347_, 0, v_toSeqRight_1338_);
v___f_1348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1348_, 0, v_toSeqLeft_1337_);
v___f_1349_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1349_, 0, v_toSeq_1336_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 4, v___f_1347_);
lean_ctor_set(v___x_1340_, 3, v___f_1348_);
lean_ctor_set(v___x_1340_, 2, v___f_1349_);
lean_ctor_set(v___x_1340_, 1, v___f_1342_);
lean_ctor_set(v___x_1340_, 0, v___x_1346_);
v___x_1351_ = v___x_1340_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___f_1342_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___f_1349_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v___f_1348_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___f_1347_);
v___x_1351_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___f_1343_);
lean_ctor_set(v___x_1333_, 0, v___x_1351_);
v___x_1353_ = v___x_1333_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___f_1343_);
v___x_1353_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v_toApplicative_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1386_; 
v___x_1354_ = l_StateRefT_x27_instMonad___redArg(v___x_1353_);
v_toApplicative_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1354_, 1);
lean_dec(v_unused_1387_);
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1386_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_toApplicative_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1386_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_toFunctor_1359_; lean_object* v_toSeq_1360_; lean_object* v_toSeqLeft_1361_; lean_object* v_toSeqRight_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1384_; 
v_toFunctor_1359_ = lean_ctor_get(v_toApplicative_1355_, 0);
v_toSeq_1360_ = lean_ctor_get(v_toApplicative_1355_, 2);
v_toSeqLeft_1361_ = lean_ctor_get(v_toApplicative_1355_, 3);
v_toSeqRight_1362_ = lean_ctor_get(v_toApplicative_1355_, 4);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_toApplicative_1355_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v_toApplicative_1355_, 1);
lean_dec(v_unused_1385_);
v___x_1364_ = v_toApplicative_1355_;
v_isShared_1365_ = v_isSharedCheck_1384_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_toSeqRight_1362_);
lean_inc(v_toSeqLeft_1361_);
lean_inc(v_toSeq_1360_);
lean_inc(v_toFunctor_1359_);
lean_dec(v_toApplicative_1355_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1384_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___f_1371_; lean_object* v___f_1372_; lean_object* v___f_1373_; lean_object* v___x_1375_; 
v___f_1366_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1367_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1359_);
v___f_1368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1368_, 0, v_toFunctor_1359_);
v___f_1369_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1369_, 0, v_toFunctor_1359_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___f_1368_);
lean_ctor_set(v___x_1370_, 1, v___f_1369_);
v___f_1371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1371_, 0, v_toSeqRight_1362_);
v___f_1372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1372_, 0, v_toSeqLeft_1361_);
v___f_1373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1373_, 0, v_toSeq_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v___f_1371_);
lean_ctor_set(v___x_1364_, 3, v___f_1372_);
lean_ctor_set(v___x_1364_, 2, v___f_1373_);
lean_ctor_set(v___x_1364_, 1, v___f_1366_);
lean_ctor_set(v___x_1364_, 0, v___x_1370_);
v___x_1375_ = v___x_1364_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___f_1366_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v___f_1373_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v___f_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v___f_1371_);
v___x_1375_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v___f_1367_);
lean_ctor_set(v___x_1357_, 0, v___x_1375_);
v___x_1377_ = v___x_1357_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___f_1367_);
v___x_1377_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_45175__overap_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_instInhabitedOfMonad___redArg(v___x_1377_, v___x_1378_);
v___x_45175__overap_1380_ = lean_panic_fn_borrowed(v___x_1379_, v_msg_1297_);
lean_dec(v___x_1379_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
v___x_1381_ = lean_apply_7(v___x_45175__overap_1380_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, lean_box(0));
return v___x_1381_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_1409_, lean_object* v_opt_1410_){
_start:
{
lean_object* v_name_1411_; lean_object* v_defValue_1412_; lean_object* v_map_1413_; lean_object* v___x_1414_; 
v_name_1411_ = lean_ctor_get(v_opt_1410_, 0);
v_defValue_1412_ = lean_ctor_get(v_opt_1410_, 1);
v_map_1413_ = lean_ctor_get(v_opts_1409_, 0);
v___x_1414_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1413_, v_name_1411_);
if (lean_obj_tag(v___x_1414_) == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_unbox(v_defValue_1412_);
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; 
v_val_1416_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v___x_1414_, 1);
if (lean_obj_tag(v_val_1416_) == 1)
{
uint8_t v_v_1417_; 
v_v_1417_ = lean_ctor_get_uint8(v_val_1416_, 0);
lean_dec_ref_known(v_val_1416_, 0);
return v_v_1417_;
}
else
{
uint8_t v___x_1418_; 
lean_dec(v_val_1416_);
v___x_1418_ = lean_unbox(v_defValue_1412_);
return v___x_1418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_1419_, lean_object* v_opt_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_1419_, v_opt_1420_);
lean_dec_ref(v_opt_1420_);
lean_dec_ref(v_opts_1419_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_box(1);
v___x_1424_ = l_Lean_MessageData_ofFormat(v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_1429_ = l_Lean_MessageData_ofFormat(v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
if (lean_obj_tag(v_x_1431_) == 0)
{
return v_x_1430_;
}
else
{
lean_object* v_head_1432_; lean_object* v_tail_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1455_; 
v_head_1432_ = lean_ctor_get(v_x_1431_, 0);
v_tail_1433_ = lean_ctor_get(v_x_1431_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1431_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1435_ = v_x_1431_;
v_isShared_1436_ = v_isSharedCheck_1455_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_tail_1433_);
lean_inc(v_head_1432_);
lean_dec(v_x_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1455_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_before_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1453_; 
v_before_1437_ = lean_ctor_get(v_head_1432_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_head_1432_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_head_1432_, 1);
lean_dec(v_unused_1454_);
v___x_1439_ = v_head_1432_;
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_before_1437_);
lean_dec(v_head_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 7);
lean_ctor_set(v___x_1439_, 1, v___x_1441_);
lean_ctor_set(v___x_1439_, 0, v_x_1430_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_x_1430_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 7);
lean_ctor_set(v___x_1435_, 1, v___x_1444_);
lean_ctor_set(v___x_1435_, 0, v___x_1443_);
v___x_1446_ = v___x_1435_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = l_Lean_MessageData_ofSyntax(v_before_1437_);
v___x_1448_ = l_Lean_indentD(v___x_1447_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1446_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v_x_1430_ = v___x_1449_;
v_x_1431_ = v_tail_1433_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1460_ = l_Lean_MessageData_ofFormat(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1461_, lean_object* v_macroStack_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1465_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1463_);
v___x_1466_ = l_Lean_Elab_pp_macroStack;
v___x_1467_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v___x_1465_, v___x_1466_);
lean_dec_ref(v___x_1465_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_macroStack_1462_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_msgData_1461_);
return v___x_1468_;
}
else
{
if (lean_obj_tag(v_macroStack_1462_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_msgData_1461_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_after_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1486_; 
v_head_1470_ = lean_ctor_get(v_macroStack_1462_, 0);
lean_inc(v_head_1470_);
v_after_1471_ = lean_ctor_get(v_head_1470_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_head_1470_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_head_1470_, 0);
lean_dec(v_unused_1487_);
v___x_1473_ = v_head_1470_;
v_isShared_1474_ = v_isSharedCheck_1486_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_after_1471_);
lean_dec(v_head_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1486_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set_tag(v___x_1473_, 7);
lean_ctor_set(v___x_1473_, 1, v___x_1475_);
lean_ctor_set(v___x_1473_, 0, v_msgData_1461_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_msgData_1461_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_msgData_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1478_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_MessageData_ofSyntax(v_after_1471_);
v___x_1481_ = l_Lean_indentD(v___x_1480_);
v_msgData_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1482_, 0, v___x_1479_);
lean_ctor_set(v_msgData_1482_, 1, v___x_1481_);
v___x_1483_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_1482_, v_macroStack_1462_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1488_, lean_object* v_macroStack_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1488_, v_macroStack_1489_, v___y_1490_);
lean_dec_ref(v___y_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_env_1500_; lean_object* v___x_1501_; lean_object* v_toCold_1502_; lean_object* v_mctx_1503_; lean_object* v_lctx_1504_; lean_object* v_options_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1499_ = lean_st_ref_get(v___y_1497_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1501_ = lean_st_ref_get(v___y_1495_);
v_toCold_1502_ = lean_ctor_get(v___y_1496_, 0);
v_mctx_1503_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_mctx_1503_);
lean_dec(v___x_1501_);
v_lctx_1504_ = lean_ctor_get(v___y_1494_, 2);
v_options_1505_ = lean_ctor_get(v_toCold_1502_, 2);
lean_inc_ref(v_options_1505_);
lean_inc_ref(v_lctx_1504_);
v___x_1506_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1506_, 0, v_env_1500_);
lean_ctor_set(v___x_1506_, 1, v_mctx_1503_);
lean_ctor_set(v___x_1506_, 2, v_lctx_1504_);
lean_ctor_set(v___x_1506_, 3, v_options_1505_);
v___x_1507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_msgData_1493_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_ref_1524_; lean_object* v_macroStack_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_ref_1524_ = lean_ctor_get(v___y_1521_, 2);
v_macroStack_1525_ = lean_ctor_get(v___y_1517_, 1);
v___x_1526_ = l_Lean_Elab_getBetterRef(v_ref_1524_, v_macroStack_1525_);
v___x_1527_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1516_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
lean_inc(v_macroStack_1525_);
v___x_1529_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1528_, v_macroStack_1525_, v___y_1521_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1526_);
lean_ctor_set(v___x_1534_, 1, v_a_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 1);
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1557_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1558_ = lean_unsigned_to_nat(11u);
v___x_1559_ = lean_unsigned_to_nat(122u);
v___x_1560_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1561_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1562_ = l_mkPanicMessageWithDecl(v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_, v___x_1557_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1579_; lean_object* v_env_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = lean_st_ref_get(v___y_1569_);
v_env_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_ref(v_env_1580_);
lean_dec(v___x_1579_);
v___x_1581_ = 0;
lean_inc(v_constName_1563_);
v___x_1582_ = l_Lean_Environment_findAsync_x3f(v_env_1580_, v_constName_1563_, v___x_1581_);
if (lean_obj_tag(v___x_1582_) == 1)
{
lean_object* v_val_1583_; uint8_t v_kind_1584_; 
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_kind_1584_ = lean_ctor_get_uint8(v_val_1583_, sizeof(void*)*3);
if (v_kind_1584_ == 6)
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1583_);
if (lean_obj_tag(v___x_1585_) == 6)
{
lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_constName_1563_);
v_val_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 0);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_val_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___x_1585_);
v___x_1594_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1595_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1594_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_a_1596_) == 0)
{
lean_del_object(v___x_1598_);
goto v___jp_1571_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
lean_dec(v_constName_1563_);
v_val_1600_ = lean_ctor_get(v_a_1596_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_a_1596_, 1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_val_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_constName_1563_);
v_a_1605_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1595_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1595_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_dec(v_val_1583_);
goto v___jp_1571_;
}
}
else
{
lean_dec(v___x_1582_);
goto v___jp_1571_;
}
v___jp_1571_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1572_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1573_ = 0;
v___x_1574_ = l_Lean_MessageData_ofConstName(v_constName_1563_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1572_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1577_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_constName_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_indVal_1623_, lean_object* v_auxFunName_1624_, lean_object* v_as_x27_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (lean_obj_tag(v_as_x27_1625_) == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_b_1626_);
return v___x_1634_;
}
else
{
lean_object* v_head_1635_; lean_object* v_tail_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v_alts_1639_; lean_object* v___x_1640_; 
v_head_1635_ = lean_ctor_get(v_as_x27_1625_, 0);
v_tail_1636_ = lean_ctor_get(v_as_x27_1625_, 1);
v___f_1637_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_1638_ = lean_unsigned_to_nat(0u);
v_alts_1639_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc(v_head_1635_);
v___x_1640_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_head_1635_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v_toConstantVal_1642_; lean_object* v_numFields_1643_; lean_object* v_type_1644_; lean_object* v___f_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v_toConstantVal_1642_ = lean_ctor_get(v_a_1641_, 0);
lean_inc_ref(v_toConstantVal_1642_);
v_numFields_1643_ = lean_ctor_get(v_a_1641_, 4);
lean_inc(v_numFields_1643_);
lean_dec(v_a_1641_);
v_type_1644_ = lean_ctor_get(v_toConstantVal_1642_, 2);
lean_inc_ref(v_type_1644_);
lean_dec_ref(v_toConstantVal_1642_);
lean_inc(v_head_1635_);
lean_inc(v_auxFunName_1624_);
lean_inc_ref(v_indVal_1623_);
v___f_1645_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1645_, 0, v_indVal_1623_);
lean_closure_set(v___f_1645_, 1, v___x_1638_);
lean_closure_set(v___f_1645_, 2, v_alts_1639_);
lean_closure_set(v___f_1645_, 3, v_numFields_1643_);
lean_closure_set(v___f_1645_, 4, v_auxFunName_1624_);
lean_closure_set(v___f_1645_, 5, v___f_1637_);
lean_closure_set(v___f_1645_, 6, v_head_1635_);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_1644_, v___f_1645_, v___x_1646_, v___x_1646_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = lean_array_push(v_b_1626_, v_a_1648_);
v_as_x27_1625_ = v_tail_1636_;
v_b_1626_ = v___x_1649_;
goto _start;
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_b_1626_);
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v_a_1651_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1647_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_b_1626_);
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v_a_1659_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1640_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1640_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1667_, lean_object* v_auxFunName_1668_, lean_object* v_as_x27_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1667_, v_auxFunName_1668_, v_as_x27_1669_, v_b_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v_as_x27_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_bs_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1682_ == 0)
{
return v_bs_1681_;
}
else
{
lean_object* v_v_1683_; lean_object* v___x_1684_; lean_object* v_bs_x27_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v_v_1683_ = lean_array_uget(v_bs_1681_, v_i_1680_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_bs_x27_1685_ = lean_array_uset(v_bs_1681_, v_i_1680_, v___x_1684_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1680_, v___x_1686_);
v___x_1688_ = lean_array_uset(v_bs_x27_1685_, v_i_1680_, v_v_1683_);
v_i_1680_ = v___x_1687_;
v_bs_1681_ = v___x_1688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_bs_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1693_, v_i_boxed_1694_, v_bs_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object* v_indVal_1696_, lean_object* v_auxFunName_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_ctors_1705_; lean_object* v_alts_1706_; lean_object* v___x_1707_; 
v_ctors_1705_ = lean_ctor_get(v_indVal_1696_, 4);
v_alts_1706_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc_ref(v_indVal_1696_);
v___x_1707_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1696_, v_auxFunName_1697_, v_ctors_1705_, v_alts_1706_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_1696_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec_ref(v_indVal_1696_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1721_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; size_t v_sz_1715_; size_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1714_ = lean_array_push(v_a_1708_, v_a_1710_);
v_sz_1715_ = lean_array_size(v___x_1714_);
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_1715_, v___x_1716_, v___x_1714_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1717_);
v___x_1719_ = v___x_1712_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1708_);
v_a_1722_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1709_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1709_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_dec_ref(v_indVal_1696_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1730_, lean_object* v_auxFunName_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1730_, v_auxFunName_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object* v_upperBound_1740_, lean_object* v_inst_1741_, lean_object* v_R_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v_c_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1740_, v_a_1743_, v_b_1744_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_upperBound_1754_, lean_object* v_inst_1755_, lean_object* v_R_1756_, lean_object* v_a_1757_, lean_object* v_b_1758_, lean_object* v_c_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(v_upperBound_1754_, v_inst_1755_, v_R_1756_, v_a_1757_, v_b_1758_, v_c_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v_upperBound_1754_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object* v___x_1768_, lean_object* v_as_1769_, size_t v_i_1770_, size_t v_stop_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_1768_, v_as_1769_, v_i_1770_, v_stop_1771_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v___x_1780_, lean_object* v_as_1781_, lean_object* v_i_1782_, lean_object* v_stop_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_i_boxed_1791_; size_t v_stop_boxed_1792_; lean_object* v_res_1793_; 
v_i_boxed_1791_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_stop_boxed_1792_ = lean_unbox_usize(v_stop_1783_);
lean_dec(v_stop_1783_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(v___x_1780_, v_as_1781_, v_i_boxed_1791_, v_stop_boxed_1792_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v_as_1781_);
lean_dec_ref(v___x_1780_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1794_, lean_object* v_indVal_1795_, lean_object* v___x_1796_, lean_object* v_xs_1797_, lean_object* v_a_1798_, lean_object* v_auxFunName_1799_, lean_object* v_inst_1800_, lean_object* v_R_1801_, lean_object* v_a_1802_, lean_object* v_b_1803_, lean_object* v_c_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1794_, v_indVal_1795_, v___x_1796_, v_xs_1797_, v_a_1798_, v_auxFunName_1799_, v_a_1802_, v_b_1803_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1813_ = _args[0];
lean_object* v_indVal_1814_ = _args[1];
lean_object* v___x_1815_ = _args[2];
lean_object* v_xs_1816_ = _args[3];
lean_object* v_a_1817_ = _args[4];
lean_object* v_auxFunName_1818_ = _args[5];
lean_object* v_inst_1819_ = _args[6];
lean_object* v_R_1820_ = _args[7];
lean_object* v_a_1821_ = _args[8];
lean_object* v_b_1822_ = _args[9];
lean_object* v_c_1823_ = _args[10];
lean_object* v___y_1824_ = _args[11];
lean_object* v___y_1825_ = _args[12];
lean_object* v___y_1826_ = _args[13];
lean_object* v___y_1827_ = _args[14];
lean_object* v___y_1828_ = _args[15];
lean_object* v___y_1829_ = _args[16];
lean_object* v___y_1830_ = _args[17];
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(v_upperBound_1813_, v_indVal_1814_, v___x_1815_, v_xs_1816_, v_a_1817_, v_auxFunName_1818_, v_inst_1819_, v_R_1820_, v_a_1821_, v_b_1822_, v_c_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_a_1817_);
lean_dec(v___x_1815_);
lean_dec(v_upperBound_1813_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object* v_indVal_1832_, lean_object* v_auxFunName_1833_, lean_object* v_as_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v_a_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1832_, v_auxFunName_1833_, v_as_x27_1835_, v_b_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_indVal_1846_, lean_object* v_auxFunName_1847_, lean_object* v_as_1848_, lean_object* v_as_x27_1849_, lean_object* v_b_1850_, lean_object* v_a_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(v_indVal_1846_, v_auxFunName_1847_, v_as_1848_, v_as_x27_1849_, v_b_1850_, v_a_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v_as_x27_1849_);
lean_dec(v_as_1848_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1860_, lean_object* v_msg_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1870_, v_msg_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1880_, lean_object* v_macroStack_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1880_, v_macroStack_1881_, v___y_1886_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1890_, lean_object* v_macroStack_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1890_, v_macroStack_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object* v_header_1913_, lean_object* v_indVal_1914_, lean_object* v_auxFunName_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; 
lean_inc_ref(v_indVal_1914_);
v___x_1923_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1913_, v_indVal_1914_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1914_, v_auxFunName_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1956_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1956_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1956_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_ref_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_ref_1930_ = lean_ctor_get(v_a_1920_, 2);
v___x_1931_ = 0;
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_ref_1930_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_1932_, 6);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
v___x_1936_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1937_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1932_);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
lean_ctor_set(v___x_1938_, 2, v___x_1937_);
v_sz_1939_ = lean_array_size(v_a_1924_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1939_, v___x_1940_, v_a_1924_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1943_ = l_Lean_mkSepArray(v___x_1941_, v___x_1942_);
lean_dec_ref(v___x_1941_);
v___x_1944_ = l_Array_append___redArg(v___x_1937_, v___x_1943_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1932_);
lean_ctor_set(v___x_1945_, 1, v___x_1936_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
v___x_1946_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_1947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1932_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_1949_ = l_Array_append___redArg(v___x_1937_, v_a_1926_);
lean_dec(v_a_1926_);
v___x_1950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1932_);
lean_ctor_set(v___x_1950_, 1, v___x_1936_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
v___x_1951_ = l_Lean_Syntax_node1(v___x_1932_, v___x_1948_, v___x_1950_);
lean_inc_ref(v___x_1938_);
v___x_1952_ = l_Lean_Syntax_node6(v___x_1932_, v___x_1934_, v___x_1935_, v___x_1938_, v___x_1938_, v___x_1945_, v___x_1947_, v___x_1951_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1952_);
v___x_1954_ = v___x_1928_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1924_);
v_a_1957_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1925_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1925_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_auxFunName_1915_);
lean_dec_ref(v_indVal_1914_);
v_a_1965_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1923_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1923_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object* v_header_1973_, lean_object* v_indVal_1974_, lean_object* v_auxFunName_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_1973_, v_indVal_1974_, v_auxFunName_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_37390__overap_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0);
v___x_37390__overap_1994_ = lean_panic_fn_borrowed(v___x_1993_, v_msg_1985_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
v___x_1995_ = lean_apply_7(v___x_37390__overap_1994_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, lean_box(0));
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v_msg_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object* v___x_2005_, lean_object* v_as_2006_, size_t v_i_2007_, size_t v_stop_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_eq(v_i_2007_, v_stop_2008_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = 1;
v___x_2016_ = lean_array_uget_borrowed(v_as_2006_, v_i_2007_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
lean_inc(v___x_2016_);
v___x_2017_ = lean_infer_type(v___x_2016_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2030_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Expr_containsFVar(v_a_2018_, v___x_2005_);
lean_dec(v_a_2018_);
if (v___x_2022_ == 0)
{
size_t v___x_2023_; size_t v___x_2024_; 
lean_del_object(v___x_2020_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2007_, v___x_2023_);
v_i_2007_ = v___x_2024_;
goto _start;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_box(v___x_2015_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2026_);
v___x_2028_ = v___x_2020_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_a_2031_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2017_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2017_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = 0;
v___x_2040_ = lean_box(v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object* v___x_2042_, lean_object* v_as_2043_, lean_object* v_i_2044_, lean_object* v_stop_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
size_t v_i_boxed_2051_; size_t v_stop_boxed_2052_; lean_object* v_res_2053_; 
v_i_boxed_2051_ = lean_unbox_usize(v_i_2044_);
lean_dec(v_i_2044_);
v_stop_boxed_2052_ = lean_unbox_usize(v_stop_2045_);
lean_dec(v_stop_2045_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2042_, v_as_2043_, v_i_boxed_2051_, v_stop_boxed_2052_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v_as_2043_);
lean_dec(v___x_2042_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object* v_upperBound_2055_, lean_object* v_indVal_2056_, lean_object* v___x_2057_, lean_object* v_xs_2058_, lean_object* v_a_2059_, lean_object* v___x_2060_, lean_object* v_auxFunName_2061_, lean_object* v_a_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_nat_dec_lt(v_a_2062_, v_upperBound_2055_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_b_2063_);
return v___x_2072_;
}
else
{
lean_object* v_snd_2073_; lean_object* v_snd_2074_; lean_object* v_fst_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2406_; 
v_snd_2073_ = lean_ctor_get(v_b_2063_, 1);
lean_inc(v_snd_2073_);
v_snd_2074_ = lean_ctor_get(v_snd_2073_, 1);
lean_inc(v_snd_2074_);
v_fst_2075_ = lean_ctor_get(v_b_2063_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_b_2063_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v_b_2063_, 1);
lean_dec(v_unused_2407_);
v___x_2077_ = v_b_2063_;
v_isShared_2078_ = v_isSharedCheck_2406_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_fst_2075_);
lean_dec(v_b_2063_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2406_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2404_; 
v_fst_2079_ = lean_ctor_get(v_snd_2073_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_snd_2073_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_snd_2073_, 1);
lean_dec(v_unused_2405_);
v___x_2081_ = v_snd_2073_;
v_isShared_2082_ = v_isSharedCheck_2404_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_fst_2079_);
lean_dec(v_snd_2073_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2404_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_fst_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2403_; 
v_fst_2083_ = lean_ctor_get(v_snd_2074_, 0);
v_snd_2084_ = lean_ctor_get(v_snd_2074_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_snd_2074_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2086_ = v_snd_2074_;
v_isShared_2087_ = v_isSharedCheck_2403_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_inc(v_fst_2083_);
lean_dec(v_snd_2074_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2403_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_numParams_2088_; lean_object* v___x_2089_; lean_object* v_a_2091_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_numParams_2088_ = lean_ctor_get(v_indVal_2056_, 1);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_instInhabitedExpr;
v___x_2095_ = lean_nat_add(v_numParams_2088_, v___x_2057_);
v___x_2096_ = lean_nat_sub(v___x_2095_, v_a_2062_);
lean_dec(v___x_2095_);
v___x_2097_ = lean_nat_sub(v___x_2096_, v___x_2089_);
lean_dec(v___x_2096_);
v___x_2098_ = lean_array_get_borrowed(v___x_2094_, v_xs_2058_, v___x_2097_);
v___x_2099_ = l_Lean_Expr_fvarId_x21(v___x_2098_);
v___x_2100_ = l_Lean_Expr_containsFVar(v_a_2059_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_inc(v___x_2099_);
v___x_2101_ = l_Lean_FVarId_getUserName___redArg(v___x_2099_, v___y_2066_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_n(v_a_2102_, 2);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l_Lean_Core_mkFreshUserName(v_a_2102_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = l_Lean_mkIdent(v_a_2104_);
v___x_2106_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0));
v___x_2107_ = lean_name_append_after(v_a_2102_, v___x_2106_);
v___x_2108_ = l_Lean_Core_mkFreshUserName(v___x_2107_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v_a_2114_; lean_object* v___x_2167_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l_Lean_mkIdent(v_a_2109_);
lean_inc(v___x_2105_);
v___x_2111_ = lean_array_push(v_fst_2075_, v___x_2105_);
lean_inc(v___x_2110_);
v___x_2112_ = lean_array_push(v_fst_2079_, v___x_2110_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v___x_2098_);
v___x_2167_ = lean_infer_type(v___x_2098_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_n(v_a_2168_, 2);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l_Lean_Meta_isProp(v_a_2168_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_unbox(v_a_2170_);
if (v___x_2171_ == 0)
{
uint8_t v___x_2172_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v_lower_2282_; lean_object* v_upper_2283_; 
v___x_2172_ = l_Lean_Expr_isAppOf(v_a_2168_, v___x_2060_);
lean_dec(v_a_2168_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
lean_dec(v_a_2170_);
v___x_2291_ = lean_nat_add(v___x_2097_, v___x_2089_);
lean_dec(v___x_2097_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = lean_array_get_size(v_xs_2058_);
v___x_2294_ = lean_nat_dec_le(v___x_2291_, v___x_2292_);
if (v___x_2294_ == 0)
{
v_lower_2282_ = v___x_2291_;
v_upper_2283_ = v___x_2293_;
goto v___jp_2281_;
}
else
{
lean_dec(v___x_2291_);
v_lower_2282_ = v___x_2292_;
v_upper_2283_ = v___x_2293_;
goto v___jp_2281_;
}
}
else
{
uint8_t v___x_2295_; 
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
v___x_2295_ = lean_unbox(v_snd_2084_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_a_2170_);
v___x_2296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_n(v_a_2297_, 4);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2299_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2061_);
v___x_2300_ = l_Lean_mkIdent(v_auxFunName_2061_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2302_ = l_Lean_Syntax_node2(v_a_2297_, v___x_2301_, v___x_2105_, v___x_2110_);
v___x_2303_ = l_Lean_Syntax_node2(v_a_2297_, v___x_2299_, v___x_2300_, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2297_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_node3(v_a_2297_, v___x_2298_, v___x_2303_, v___x_2305_, v_fst_2083_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_snd_2084_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2112_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2111_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v_a_2091_ = v___x_2309_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2310_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2296_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2296_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v___x_2318_; 
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
v___x_2318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc_n(v_a_2319_, 2);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2061_);
v___x_2321_ = l_Lean_mkIdent(v_auxFunName_2061_);
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2323_ = l_Lean_Syntax_node2(v_a_2319_, v___x_2322_, v___x_2105_, v___x_2110_);
v___x_2324_ = l_Lean_Syntax_node2(v_a_2319_, v___x_2320_, v___x_2321_, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v_a_2170_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2112_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2111_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v_a_2091_ = v___x_2327_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2170_);
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2328_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2318_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2318_);
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
v___jp_2173_:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_nat_dec_lt(v___y_2175_, v___y_2176_);
if (v___x_2177_ == 0)
{
lean_dec(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___x_2099_);
v_a_2114_ = v___x_2177_;
goto v___jp_2113_;
}
else
{
size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_usize_of_nat(v___y_2175_);
lean_dec(v___y_2175_);
v___x_2179_ = lean_usize_of_nat(v___y_2176_);
lean_dec(v___y_2176_);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2099_, v___y_2174_, v___x_2178_, v___x_2179_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___y_2174_);
lean_dec(v___x_2099_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; uint8_t v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_unbox(v_a_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
v_a_2114_ = v___x_2183_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2184_; 
lean_dec(v_a_2181_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
v___x_2184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_toCold_2185_; lean_object* v_a_2186_; lean_object* v_quotContext_2187_; lean_object* v_currMacroScope_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_toCold_2185_ = lean_ctor_get(v___y_2068_, 0);
v_a_2186_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_n(v_a_2186_, 31);
lean_dec_ref_known(v___x_2184_, 1);
v_quotContext_2187_ = lean_ctor_get(v_toCold_2185_, 8);
v_currMacroScope_2188_ = lean_ctor_get(v_toCold_2185_, 9);
v___x_2189_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_2190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_2191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2186_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_2193_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc_n(v_currMacroScope_2188_, 4);
lean_inc_n(v_quotContext_2187_, 4);
v___x_2195_ = l_Lean_addMacroScope(v_quotContext_2187_, v___x_2194_, v_currMacroScope_2188_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2186_);
lean_ctor_set(v___x_2197_, 1, v___x_2193_);
lean_ctor_set(v___x_2197_, 2, v___x_2195_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
lean_inc_ref(v___x_2197_);
v___x_2198_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2192_, v___x_2197_);
v___x_2199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_2200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2186_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2186_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Lean_Syntax_node3(v_a_2186_, v___x_2201_, v___x_2105_, v___x_2203_, v___x_2110_);
v___x_2205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_2206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2186_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_2208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_2209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2186_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_2211_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_2214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_a_2186_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
v___x_2216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_2217_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2218_, 0, v_a_2186_);
lean_ctor_set(v___x_2218_, 1, v___x_2212_);
lean_ctor_set(v___x_2218_, 2, v___x_2217_);
v___x_2219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2221_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2186_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2224_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_addMacroScope(v_quotContext_2187_, v___x_2225_, v_currMacroScope_2188_);
v___x_2227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_2228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2228_, 0, v_a_2186_);
lean_ctor_set(v___x_2228_, 1, v___x_2224_);
lean_ctor_set(v___x_2228_, 2, v___x_2226_);
lean_ctor_set(v___x_2228_, 3, v___x_2227_);
v___x_2229_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2223_, v___x_2228_);
v___x_2230_ = l_Lean_Syntax_node2(v_a_2186_, v___x_2220_, v___x_2222_, v___x_2229_);
v___x_2231_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2232_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_2233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_2234_ = l_Lean_addMacroScope(v_quotContext_2187_, v___x_2233_, v_currMacroScope_2188_);
v___x_2235_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_2236_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2186_);
lean_ctor_set(v___x_2236_, 1, v___x_2232_);
lean_ctor_set(v___x_2236_, 2, v___x_2234_);
lean_ctor_set(v___x_2236_, 3, v___x_2235_);
v___x_2237_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2212_, v___x_2197_);
v___x_2238_ = l_Lean_Syntax_node2(v_a_2186_, v___x_2231_, v___x_2236_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2186_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_Syntax_node3(v_a_2186_, v___x_2219_, v___x_2230_, v___x_2238_, v___x_2240_);
lean_inc_ref_n(v___x_2218_, 3);
v___x_2242_ = l_Lean_Syntax_node2(v_a_2186_, v___x_2216_, v___x_2218_, v___x_2241_);
v___x_2243_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2212_, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node4(v_a_2186_, v___x_2214_, v___x_2215_, v___x_2243_, v___x_2218_, v___x_2218_);
v___x_2245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_2246_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_2247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2186_);
lean_ctor_set(v___x_2247_, 1, v___x_2245_);
v___x_2248_ = l_Lean_Syntax_node2(v_a_2186_, v___x_2246_, v___x_2247_, v_fst_2083_);
v___x_2249_ = l_Lean_Syntax_node3(v_a_2186_, v___x_2212_, v___x_2244_, v___x_2218_, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2211_, v___x_2249_);
v___x_2251_ = l_Lean_Syntax_node1(v_a_2186_, v___x_2210_, v___x_2250_);
v___x_2252_ = l_Lean_Syntax_node2(v_a_2186_, v___x_2207_, v___x_2209_, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2186_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2257_ = l_Lean_addMacroScope(v_quotContext_2187_, v___x_2256_, v_currMacroScope_2188_);
v___x_2258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_2259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2259_, 0, v_a_2186_);
lean_ctor_set(v___x_2259_, 1, v___x_2255_);
lean_ctor_set(v___x_2259_, 2, v___x_2257_);
lean_ctor_set(v___x_2259_, 3, v___x_2258_);
v___x_2260_ = l_Lean_Syntax_node8(v_a_2186_, v___x_2189_, v___x_2191_, v___x_2198_, v___x_2200_, v___x_2204_, v___x_2206_, v___x_2252_, v___x_2254_, v___x_2259_);
v___x_2261_ = lean_box(v___x_2172_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2112_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2111_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v_a_2091_ = v___x_2264_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v_fst_2083_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2265_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2184_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2184_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2273_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2180_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2180_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
v___jp_2281_:
{
lean_object* v___x_2284_; lean_object* v_array_2285_; lean_object* v_start_2286_; lean_object* v_stop_2287_; uint8_t v___x_2288_; 
lean_inc_ref(v_xs_2058_);
v___x_2284_ = l_Array_toSubarray___redArg(v_xs_2058_, v_lower_2282_, v_upper_2283_);
v_array_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_array_2285_);
v_start_2286_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_start_2286_);
v_stop_2287_ = lean_ctor_get(v___x_2284_, 2);
lean_inc(v_stop_2287_);
lean_dec_ref(v___x_2284_);
v___x_2288_ = lean_nat_dec_lt(v_start_2286_, v_stop_2287_);
if (v___x_2288_ == 0)
{
lean_dec(v_stop_2287_);
lean_dec(v_start_2286_);
lean_dec_ref(v_array_2285_);
lean_dec(v___x_2099_);
v_a_2114_ = v___x_2288_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = lean_array_get_size(v_array_2285_);
v___x_2290_ = lean_nat_dec_le(v_stop_2287_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_stop_2287_);
v___y_2174_ = v_array_2285_;
v___y_2175_ = v_start_2286_;
v___y_2176_ = v___x_2289_;
goto v___jp_2173_;
}
else
{
v___y_2174_ = v_array_2285_;
v___y_2175_ = v_start_2286_;
v___y_2176_ = v_stop_2287_;
goto v___jp_2173_;
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_a_2170_);
lean_dec(v_a_2168_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_fst_2083_);
lean_ctor_set(v___x_2336_, 1, v_snd_2084_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2112_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2111_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v_a_2091_ = v___x_2338_;
goto v___jp_2090_;
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2339_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2169_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2169_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2347_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2167_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2167_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
v___jp_2113_:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_unbox(v_snd_2084_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_n(v_a_2117_, 4);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2120_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_a_2117_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_node3(v_a_2117_, v___x_2119_, v___x_2105_, v___x_2121_, v___x_2110_);
v___x_2123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2117_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_Syntax_node3(v_a_2117_, v___x_2118_, v___x_2122_, v___x_2124_, v_fst_2083_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2125_);
v___x_2127_ = v___x_2086_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_snd_2084_);
v___x_2127_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2129_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2127_);
lean_ctor_set(v___x_2081_, 0, v___x_2112_);
v___x_2129_ = v___x_2081_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2129_);
lean_ctor_set(v___x_2077_, 0, v___x_2111_);
v___x_2131_ = v___x_2077_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
v_a_2091_ = v___x_2131_;
goto v___jp_2090_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2135_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2116_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2116_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v___x_2143_; 
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
v___x_2143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc_n(v_a_2144_, 2);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2146_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_a_2144_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Syntax_node3(v_a_2144_, v___x_2145_, v___x_2105_, v___x_2147_, v___x_2110_);
v___x_2149_ = lean_box(v_a_2114_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v___x_2149_);
lean_ctor_set(v___x_2086_, 0, v___x_2148_);
v___x_2151_ = v___x_2086_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2151_);
lean_ctor_set(v___x_2081_, 0, v___x_2112_);
v___x_2153_ = v___x_2081_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2153_);
lean_ctor_set(v___x_2077_, 0, v___x_2111_);
v___x_2155_ = v___x_2077_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v_a_2091_ = v___x_2155_;
goto v___jp_2090_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v___x_2111_);
lean_dec(v___x_2110_);
lean_dec(v___x_2105_);
lean_del_object(v___x_2086_);
lean_del_object(v___x_2081_);
lean_del_object(v___x_2077_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2159_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2143_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2143_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___x_2105_);
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2077_);
lean_dec(v_fst_2075_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2355_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2108_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2108_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_a_2102_);
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2077_);
lean_dec(v_fst_2075_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2363_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2103_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2103_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2077_);
lean_dec(v_fst_2075_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2371_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2101_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2101_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
lean_object* v___x_2379_; 
lean_dec(v___x_2099_);
lean_dec(v___x_2097_);
v___x_2379_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc_n(v_a_2380_, 2);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2382_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node1(v_a_2380_, v___x_2381_, v___x_2383_);
v___x_2385_ = lean_array_push(v_fst_2075_, v___x_2384_);
if (v_isShared_2087_ == 0)
{
v___x_2387_ = v___x_2086_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_fst_2083_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_snd_2084_);
v___x_2387_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2387_);
v___x_2389_ = v___x_2081_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fst_2079_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2389_);
lean_ctor_set(v___x_2077_, 0, v___x_2385_);
v___x_2391_ = v___x_2077_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
v_a_2091_ = v___x_2391_;
goto v___jp_2090_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2077_);
lean_dec(v_fst_2075_);
lean_dec(v_a_2062_);
lean_dec(v_auxFunName_2061_);
lean_dec_ref(v_xs_2058_);
v_a_2395_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2379_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2379_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_nat_add(v_a_2062_, v___x_2089_);
lean_dec(v_a_2062_);
v_a_2062_ = v___x_2092_;
v_b_2063_ = v_a_2091_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object* v_upperBound_2408_, lean_object* v_indVal_2409_, lean_object* v___x_2410_, lean_object* v_xs_2411_, lean_object* v_a_2412_, lean_object* v___x_2413_, lean_object* v_auxFunName_2414_, lean_object* v_a_2415_, lean_object* v_b_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_2408_, v_indVal_2409_, v___x_2410_, v_xs_2411_, v_a_2412_, v___x_2413_, v_auxFunName_2414_, v_a_2415_, v_b_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___x_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2410_);
lean_dec_ref(v_indVal_2409_);
lean_dec(v_upperBound_2408_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(lean_object* v___x_2452_, uint8_t v_rhs__empty_2453_, lean_object* v_numFields_2454_, lean_object* v_indVal_2455_, lean_object* v_name_2456_, lean_object* v_auxFunName_2457_, lean_object* v___f_2458_, lean_object* v_xs_2459_, lean_object* v_type_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Core_betaReduce(v_type_2460_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_toCold_2469_; lean_object* v_a_2470_; lean_object* v_ref_2471_; lean_object* v_quotContext_2472_; lean_object* v_currMacroScope_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_toCold_2469_ = lean_ctor_get(v___y_2465_, 0);
v_a_2470_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2468_, 1);
v_ref_2471_ = lean_ctor_get(v___y_2465_, 2);
v_quotContext_2472_ = lean_ctor_get(v_toCold_2469_, 8);
v_currMacroScope_2473_ = lean_ctor_get(v_toCold_2469_, 9);
v___x_2474_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_2475_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_2476_ = lean_mk_empty_array_with_capacity(v___x_2452_);
v___x_2477_ = 0;
v___x_2478_ = l_Lean_SourceInfo_fromRef(v_ref_2471_, v___x_2477_);
lean_inc(v_currMacroScope_2473_);
lean_inc(v_quotContext_2472_);
v___x_2479_ = l_Lean_addMacroScope(v_quotContext_2472_, v___x_2475_, v_currMacroScope_2473_);
v___x_2480_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_2481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2478_);
lean_ctor_set(v___x_2481_, 1, v___x_2474_);
lean_ctor_set(v___x_2481_, 2, v___x_2479_);
lean_ctor_set(v___x_2481_, 3, v___x_2480_);
v___x_2482_ = lean_box(v_rhs__empty_2453_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
lean_inc_ref(v___x_2476_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2476_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2476_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
lean_inc(v___x_2452_);
v___x_2486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_numFields_2454_, v_indVal_2455_, v_numFields_2454_, v_xs_2459_, v_a_2470_, v_name_2456_, v_auxFunName_2457_, v___x_2452_, v___x_2485_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v_a_2470_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v_snd_2488_; lean_object* v_snd_2489_; lean_object* v_fst_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2588_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v_snd_2488_ = lean_ctor_get(v_a_2487_, 1);
lean_inc(v_snd_2488_);
v_snd_2489_ = lean_ctor_get(v_snd_2488_, 1);
lean_inc(v_snd_2489_);
v_fst_2490_ = lean_ctor_get(v_a_2487_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_a_2487_, 1);
lean_dec(v_unused_2589_);
v___x_2492_ = v_a_2487_;
v_isShared_2493_ = v_isSharedCheck_2588_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_fst_2490_);
lean_dec(v_a_2487_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2588_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_fst_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2586_; 
v_fst_2494_ = lean_ctor_get(v_snd_2488_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_snd_2488_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v_snd_2488_, 1);
lean_dec(v_unused_2587_);
v___x_2496_ = v_snd_2488_;
v_isShared_2497_ = v_isSharedCheck_2586_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_fst_2494_);
lean_dec(v_snd_2488_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2586_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_fst_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2584_; 
v_fst_2498_ = lean_ctor_get(v_snd_2489_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_snd_2489_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v_snd_2489_, 1);
lean_dec(v_unused_2585_);
v___x_2500_ = v_snd_2489_;
v_isShared_2501_ = v_isSharedCheck_2584_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_fst_2498_);
lean_dec(v_snd_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2584_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_ctorArgs1_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2553_ = lean_array_get_size(v_fst_2490_);
v___x_2554_ = lean_nat_dec_eq(v___x_2553_, v___x_2452_);
lean_dec(v___x_2452_);
if (v___x_2554_ == 0)
{
v_ctorArgs1_2503_ = v_fst_2490_;
v___y_2504_ = v___y_2461_;
v___y_2505_ = v___y_2462_;
v___y_2506_ = v___y_2463_;
v___y_2507_ = v___y_2464_;
v___y_2508_ = v___y_2465_;
v___y_2509_ = v___y_2466_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2555_; 
lean_inc_ref(v___f_2458_);
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
v___x_2555_ = lean_apply_7(v___f_2458_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, lean_box(0));
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_n(v_a_2556_, 7);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5));
v___x_2558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_a_2556_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2562_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2563_ = lean_box(0);
lean_inc(v_currMacroScope_2473_);
lean_inc(v_quotContext_2472_);
v___x_2564_ = l_Lean_addMacroScope(v_quotContext_2472_, v___x_2563_, v_currMacroScope_2473_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2556_);
lean_ctor_set(v___x_2566_, 1, v___x_2562_);
lean_ctor_set(v___x_2566_, 2, v___x_2564_);
lean_ctor_set(v___x_2566_, 3, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node1(v_a_2556_, v___x_2561_, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node2(v_a_2556_, v___x_2558_, v___x_2560_, v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2570_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2556_);
lean_ctor_set(v___x_2571_, 1, v___x_2569_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
v___x_2572_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2556_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node3(v_a_2556_, v___x_2557_, v___x_2568_, v___x_2571_, v___x_2573_);
v___x_2575_ = lean_array_push(v_fst_2490_, v___x_2574_);
v_ctorArgs1_2503_ = v___x_2575_;
v___y_2504_ = v___y_2461_;
v___y_2505_ = v___y_2462_;
v___y_2506_ = v___y_2463_;
v___y_2507_ = v___y_2464_;
v___y_2508_ = v___y_2465_;
v___y_2509_ = v___y_2466_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_fst_2494_);
lean_del_object(v___x_2492_);
lean_dec(v_fst_2490_);
lean_dec_ref(v___f_2458_);
v_a_2576_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2555_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2555_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
v___jp_2502_:
{
lean_object* v___x_2510_; 
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
v___x_2510_ = lean_apply_7(v___f_2458_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2544_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2544_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2544_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7));
v___x_2516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
lean_inc(v_a_2511_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 2);
lean_ctor_set(v___x_2500_, 1, v___x_2516_);
lean_ctor_set(v___x_2500_, 0, v_a_2511_);
v___x_2518_ = v___x_2500_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2511_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0));
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1));
lean_inc(v_a_2511_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 2);
lean_ctor_set(v___x_2496_, 1, v___x_2519_);
lean_ctor_set(v___x_2496_, 0, v_a_2511_);
v___x_2522_ = v___x_2496_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2511_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2519_);
v___x_2522_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2523_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3));
v___x_2524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2525_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2526_ = l_Array_reverse___redArg(v_ctorArgs1_2503_);
v___x_2527_ = l_Array_append___redArg(v___x_2525_, v___x_2526_);
lean_dec_ref(v___x_2526_);
v___x_2528_ = l_Array_reverse___redArg(v_fst_2494_);
v___x_2529_ = l_Array_append___redArg(v___x_2527_, v___x_2528_);
lean_dec_ref(v___x_2528_);
lean_inc_n(v_a_2511_, 3);
v___x_2530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2530_, 0, v_a_2511_);
lean_ctor_set(v___x_2530_, 1, v___x_2524_);
lean_ctor_set(v___x_2530_, 2, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2531_, 0, v_a_2511_);
lean_ctor_set(v___x_2531_, 1, v___x_2524_);
lean_ctor_set(v___x_2531_, 2, v___x_2525_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 2);
lean_ctor_set(v___x_2492_, 1, v___x_2532_);
lean_ctor_set(v___x_2492_, 0, v_a_2511_);
v___x_2534_ = v___x_2492_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2511_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_inc_n(v_a_2511_, 2);
v___x_2535_ = l_Lean_Syntax_node4(v_a_2511_, v___x_2523_, v___x_2530_, v___x_2531_, v___x_2534_, v_fst_2498_);
v___x_2536_ = l_Lean_Syntax_node2(v_a_2511_, v___x_2520_, v___x_2522_, v___x_2535_);
v___x_2537_ = l_Lean_Syntax_node2(v_a_2511_, v___x_2515_, v___x_2518_, v___x_2536_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2537_);
v___x_2539_ = v___x_2513_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_ctorArgs1_2503_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_fst_2494_);
lean_del_object(v___x_2492_);
v_a_2545_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2510_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2510_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
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
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v___f_2458_);
lean_dec(v___x_2452_);
v_a_2590_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2486_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2486_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v_xs_2459_);
lean_dec_ref(v___f_2458_);
lean_dec(v_auxFunName_2457_);
lean_dec(v___x_2452_);
v_a_2598_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2468_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2468_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object* v___x_2606_, lean_object* v_rhs__empty_2607_, lean_object* v_numFields_2608_, lean_object* v_indVal_2609_, lean_object* v_name_2610_, lean_object* v_auxFunName_2611_, lean_object* v___f_2612_, lean_object* v_xs_2613_, lean_object* v_type_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v_rhs__empty_boxed_2622_; lean_object* v_res_2623_; 
v_rhs__empty_boxed_2622_ = lean_unbox(v_rhs__empty_2607_);
v_res_2623_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(v___x_2606_, v_rhs__empty_boxed_2622_, v_numFields_2608_, v_indVal_2609_, v_name_2610_, v_auxFunName_2611_, v___f_2612_, v_xs_2613_, v_type_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v_name_2610_);
lean_dec_ref(v_indVal_2609_);
lean_dec(v_numFields_2608_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object* v___x_2624_, lean_object* v_ctors_2625_, lean_object* v___x_2626_, uint8_t v_rhs__empty_2627_, lean_object* v_indVal_2628_, lean_object* v_name_2629_, lean_object* v_auxFunName_2630_, lean_object* v___f_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = l_List_get_x21Internal___redArg(v___x_2624_, v_ctors_2625_, v_x_2632_);
v___x_2641_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v_toConstantVal_2643_; lean_object* v_numFields_2644_; lean_object* v_type_2645_; lean_object* v___x_2646_; lean_object* v___f_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v_toConstantVal_2643_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_toConstantVal_2643_);
v_numFields_2644_ = lean_ctor_get(v_a_2642_, 4);
lean_inc(v_numFields_2644_);
lean_dec(v_a_2642_);
v_type_2645_ = lean_ctor_get(v_toConstantVal_2643_, 2);
lean_inc_ref(v_type_2645_);
lean_dec_ref(v_toConstantVal_2643_);
v___x_2646_ = lean_box(v_rhs__empty_2627_);
v___f_2647_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed), 16, 7);
lean_closure_set(v___f_2647_, 0, v___x_2626_);
lean_closure_set(v___f_2647_, 1, v___x_2646_);
lean_closure_set(v___f_2647_, 2, v_numFields_2644_);
lean_closure_set(v___f_2647_, 3, v_indVal_2628_);
lean_closure_set(v___f_2647_, 4, v_name_2629_);
lean_closure_set(v___f_2647_, 5, v_auxFunName_2630_);
lean_closure_set(v___f_2647_, 6, v___f_2631_);
v___x_2648_ = 0;
v___x_2649_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_2645_, v___f_2647_, v___x_2648_, v___x_2648_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2649_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v___f_2631_);
lean_dec(v_auxFunName_2630_);
lean_dec(v_name_2629_);
lean_dec_ref(v_indVal_2628_);
lean_dec(v___x_2626_);
v_a_2650_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2641_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2641_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object* v___x_2658_, lean_object* v_ctors_2659_, lean_object* v___x_2660_, lean_object* v_rhs__empty_2661_, lean_object* v_indVal_2662_, lean_object* v_name_2663_, lean_object* v_auxFunName_2664_, lean_object* v___f_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v_rhs__empty_boxed_2674_; lean_object* v_res_2675_; 
v_rhs__empty_boxed_2674_ = lean_unbox(v_rhs__empty_2661_);
v_res_2675_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(v___x_2658_, v_ctors_2659_, v___x_2660_, v_rhs__empty_boxed_2674_, v_indVal_2662_, v_name_2663_, v_auxFunName_2664_, v___f_2665_, v_x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v_ctors_2659_);
lean_dec(v___x_2658_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object* v_f_2676_, lean_object* v_n_2677_, lean_object* v_x_2678_, lean_object* v_i_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_nat_dec_lt(v_i_2679_, v_n_2677_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec(v_i_2679_);
lean_dec_ref(v_f_2676_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_x_2678_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; 
lean_inc_ref(v_f_2676_);
lean_inc(v___y_2685_);
lean_inc_ref(v___y_2684_);
lean_inc(v___y_2683_);
lean_inc_ref(v___y_2682_);
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v_i_2679_);
v___x_2689_ = lean_apply_8(v_f_2676_, v_i_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, lean_box(0));
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = lean_array_push(v_x_2678_, v_a_2690_);
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_add(v_i_2679_, v___x_2692_);
lean_dec(v_i_2679_);
v_x_2678_ = v___x_2691_;
v_i_2679_ = v___x_2693_;
goto _start;
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_i_2679_);
lean_dec_ref(v_x_2678_);
lean_dec_ref(v_f_2676_);
v_a_2695_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2689_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2689_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object* v_f_2703_, lean_object* v_n_2704_, lean_object* v_x_2705_, lean_object* v_i_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2703_, v_n_2704_, v_x_2705_, v_i_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_n_2704_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object* v_n_2715_, lean_object* v_f_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_mk_empty_array_with_capacity(v_n_2715_);
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2716_, v_n_2715_, v___x_2724_, v___x_2725_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object* v_n_2727_, lean_object* v_f_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_2727_, v_f_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v_n_2727_);
return v_res_2736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2));
v___x_2741_ = lean_unsigned_to_nat(2u);
v___x_2742_ = lean_unsigned_to_nat(113u);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1));
v___x_2744_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0));
v___x_2745_ = l_mkPanicMessageWithDecl(v___x_2744_, v___x_2743_, v___x_2742_, v___x_2741_, v___x_2740_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8));
v___x_2757_ = l_String_toRawSubstring_x27(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20));
v___x_2783_ = l_String_toRawSubstring_x27(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27));
v___x_2798_ = l_String_toRawSubstring_x27(v___x_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33));
v___x_2812_ = l_String_toRawSubstring_x27(v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object* v_header_2821_, lean_object* v_indVal_2822_, lean_object* v_auxFunName_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_targetNames_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_3026_; 
v_targetNames_2831_ = lean_ctor_get(v_header_2821_, 2);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_header_2821_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; lean_object* v_unused_3028_; lean_object* v_unused_3029_; 
v_unused_3027_ = lean_ctor_get(v_header_2821_, 3);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_header_2821_, 1);
lean_dec(v_unused_3028_);
v_unused_3029_ = lean_ctor_get(v_header_2821_, 0);
lean_dec(v_unused_3029_);
v___x_2833_ = v_header_2821_;
v_isShared_2834_ = v_isSharedCheck_3026_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_targetNames_2831_);
lean_dec(v_header_2821_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_3026_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v_rhs__empty_2837_; 
v___x_2835_ = lean_array_get_size(v_targetNames_2831_);
v___x_2836_ = lean_unsigned_to_nat(2u);
v_rhs__empty_2837_ = lean_nat_dec_eq(v___x_2835_, v___x_2836_);
if (v_rhs__empty_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2833_);
lean_dec_ref(v_targetNames_2831_);
lean_dec(v_auxFunName_2823_);
lean_dec_ref(v_indVal_2822_);
v___x_2838_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3);
v___x_2839_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v___x_2838_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
return v___x_2839_;
}
else
{
lean_object* v_toConstantVal_2840_; lean_object* v_ctors_2841_; lean_object* v_name_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_3023_; 
v_toConstantVal_2840_ = lean_ctor_get(v_indVal_2822_, 0);
lean_inc_ref(v_toConstantVal_2840_);
v_ctors_2841_ = lean_ctor_get(v_indVal_2822_, 4);
v_name_2842_ = lean_ctor_get(v_toConstantVal_2840_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_toConstantVal_2840_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3024_ = lean_ctor_get(v_toConstantVal_2840_, 2);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_toConstantVal_2840_, 1);
lean_dec(v_unused_3025_);
v___x_2844_ = v_toConstantVal_2840_;
v_isShared_2845_ = v_isSharedCheck_3023_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_name_2842_);
lean_dec(v_toConstantVal_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_3023_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___f_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v_x1_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v_x2_2853_; lean_object* v___x_2854_; lean_object* v___f_2855_; lean_object* v_ctorIdxName_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2846_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = lean_array_get_borrowed(v___x_2847_, v_targetNames_2831_, v___x_2848_);
lean_inc(v___x_2849_);
v_x1_2850_ = l_Lean_mkIdent(v___x_2849_);
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = lean_array_get(v___x_2847_, v_targetNames_2831_, v___x_2851_);
lean_dec_ref(v_targetNames_2831_);
v_x2_2853_ = l_Lean_mkIdent(v___x_2852_);
v___x_2854_ = lean_box(v_rhs__empty_2837_);
lean_inc_n(v_name_2842_, 3);
lean_inc_ref(v_indVal_2822_);
lean_inc(v_ctors_2841_);
v___f_2855_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2855_, 0, v___x_2847_);
lean_closure_set(v___f_2855_, 1, v_ctors_2841_);
lean_closure_set(v___f_2855_, 2, v___x_2848_);
lean_closure_set(v___f_2855_, 3, v___x_2854_);
lean_closure_set(v___f_2855_, 4, v_indVal_2822_);
lean_closure_set(v___f_2855_, 5, v_name_2842_);
lean_closure_set(v___f_2855_, 6, v_auxFunName_2823_);
lean_closure_set(v___f_2855_, 7, v___f_2846_);
v_ctorIdxName_2856_ = l_Lean_mkCtorIdxName(v_name_2842_);
v___x_2857_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5));
v___x_2858_ = l_Lean_Name_append(v_name_2842_, v___x_2857_);
v___x_2859_ = l_Lean_Core_mkFreshUserName(v___x_2858_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc_n(v_a_2860_, 2);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_mkCasesOnSameCtor(v_a_2860_, v_name_2842_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref_known(v___x_2861_, 1);
v___x_2862_ = l_Lean_InductiveVal_numCtors(v_indVal_2822_);
lean_dec_ref(v_indVal_2822_);
v___x_2863_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v___x_2862_, v___f_2855_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2998_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2998_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2998_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_nat_dec_eq(v___x_2862_, v___x_2851_);
lean_dec(v___x_2862_);
if (v___x_2868_ == 0)
{
lean_object* v_toCold_2869_; lean_object* v_ref_2870_; lean_object* v_quotContext_2871_; lean_object* v_currMacroScope_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v_toCold_2869_ = lean_ctor_get(v_a_2828_, 0);
v_ref_2870_ = lean_ctor_get(v_a_2828_, 2);
v_quotContext_2871_ = lean_ctor_get(v_toCold_2869_, 8);
v_currMacroScope_2872_ = lean_ctor_get(v_toCold_2869_, 9);
v___x_2873_ = l_Lean_SourceInfo_fromRef(v_ref_2870_, v___x_2868_);
v___x_2874_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_2875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_2873_, 2);
v___x_2876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2873_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2878_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 1);
lean_ctor_set(v___x_2844_, 2, v___x_2878_);
lean_ctor_set(v___x_2844_, 1, v___x_2877_);
lean_ctor_set(v___x_2844_, 0, v___x_2873_);
v___x_2880_ = v___x_2844_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7));
v___x_2882_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2883_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9);
v___x_2884_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12));
lean_inc(v_currMacroScope_2872_);
lean_inc(v_quotContext_2871_);
v___x_2885_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2884_, v_currMacroScope_2872_);
v___x_2886_ = lean_box(0);
v___x_2887_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16));
lean_inc(v___x_2873_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 3);
lean_ctor_set(v___x_2833_, 3, v___x_2887_);
lean_ctor_set(v___x_2833_, 2, v___x_2885_);
lean_ctor_set(v___x_2833_, 1, v___x_2883_);
lean_ctor_set(v___x_2833_, 0, v___x_2873_);
v___x_2889_ = v___x_2833_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2892_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v___x_2873_, 41);
v___x_2893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2873_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2895_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
lean_inc_n(v_currMacroScope_2872_, 5);
lean_inc_n(v_quotContext_2871_, 5);
v___x_2896_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2847_, v_currMacroScope_2872_);
v___x_2897_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2898_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2873_);
lean_ctor_set(v___x_2898_, 1, v___x_2895_);
lean_ctor_set(v___x_2898_, 2, v___x_2896_);
lean_ctor_set(v___x_2898_, 3, v___x_2897_);
v___x_2899_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2894_, v___x_2898_);
v___x_2900_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2891_, v___x_2893_, v___x_2899_);
v___x_2901_ = l_Lean_mkCIdent(v_ctorIdxName_2856_);
lean_inc(v_x1_2850_);
v___x_2902_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v_x1_2850_);
lean_inc(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2901_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2873_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
lean_inc_ref(v___x_2905_);
lean_inc(v___x_2900_);
v___x_2906_ = l_Lean_Syntax_node3(v___x_2873_, v___x_2890_, v___x_2900_, v___x_2903_, v___x_2905_);
lean_inc(v_x2_2853_);
v___x_2907_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v_x2_2853_);
v___x_2908_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2901_, v___x_2907_);
v___x_2909_ = l_Lean_Syntax_node3(v___x_2873_, v___x_2890_, v___x_2900_, v___x_2908_, v___x_2905_);
v___x_2910_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2877_, v___x_2906_, v___x_2909_);
v___x_2911_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2889_, v___x_2910_);
lean_inc_ref_n(v___x_2880_, 2);
v___x_2912_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2881_, v___x_2880_, v___x_2911_);
v___x_2913_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2912_);
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2873_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_2918_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
v___x_2919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2873_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18));
v___x_2921_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19));
v___x_2922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2873_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21);
v___x_2924_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22));
v___x_2925_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2924_, v_currMacroScope_2872_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26));
v___x_2927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2873_);
lean_ctor_set(v___x_2927_, 1, v___x_2923_);
lean_ctor_set(v___x_2927_, 2, v___x_2925_);
lean_ctor_set(v___x_2927_, 3, v___x_2926_);
lean_inc_ref(v___x_2922_);
v___x_2928_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2920_, v___x_2922_, v___x_2927_);
v___x_2929_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2930_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
v___x_2931_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2930_, v_currMacroScope_2872_);
v___x_2932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2873_);
lean_ctor_set(v___x_2932_, 1, v___x_2929_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
lean_ctor_set(v___x_2932_, 3, v___x_2886_);
lean_inc_ref(v___x_2932_);
v___x_2933_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2932_);
v___x_2934_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2928_, v___x_2933_);
v___x_2935_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2935_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_2938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2873_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = l_Lean_mkCIdent(v_a_2860_);
v___x_2940_ = l_Array_mkArray3___redArg(v_x1_2850_, v_x2_2853_, v___x_2932_);
v___x_2941_ = l_Array_append___redArg(v___x_2940_, v_a_2864_);
lean_dec(v_a_2864_);
v___x_2942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2873_);
lean_ctor_set(v___x_2942_, 1, v___x_2877_);
lean_ctor_set(v___x_2942_, 2, v___x_2941_);
v___x_2943_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2939_, v___x_2942_);
lean_inc_ref(v___x_2938_);
lean_inc_ref(v___x_2919_);
v___x_2944_ = l_Lean_Syntax_node4(v___x_2873_, v___x_2917_, v___x_2919_, v___x_2936_, v___x_2938_, v___x_2943_);
v___x_2945_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28);
v___x_2946_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29));
v___x_2947_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2946_, v_currMacroScope_2872_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32));
v___x_2949_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2873_);
lean_ctor_set(v___x_2949_, 1, v___x_2945_);
lean_ctor_set(v___x_2949_, 2, v___x_2947_);
lean_ctor_set(v___x_2949_, 3, v___x_2948_);
v___x_2950_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2920_, v___x_2922_, v___x_2949_);
v___x_2951_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2873_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2951_, v___x_2953_);
v___x_2955_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2954_);
v___x_2956_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2882_, v___x_2950_, v___x_2955_);
v___x_2957_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2956_);
v___x_2958_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2877_, v___x_2957_);
v___x_2959_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2960_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2961_ = l_Lean_addMacroScope(v_quotContext_2871_, v___x_2960_, v_currMacroScope_2872_);
v___x_2962_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_2963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2873_);
lean_ctor_set(v___x_2963_, 1, v___x_2959_);
lean_ctor_set(v___x_2963_, 2, v___x_2961_);
lean_ctor_set(v___x_2963_, 3, v___x_2962_);
v___x_2964_ = l_Lean_Syntax_node4(v___x_2873_, v___x_2917_, v___x_2919_, v___x_2958_, v___x_2938_, v___x_2963_);
v___x_2965_ = l_Lean_Syntax_node2(v___x_2873_, v___x_2877_, v___x_2944_, v___x_2964_);
v___x_2966_ = l_Lean_Syntax_node1(v___x_2873_, v___x_2916_, v___x_2965_);
v___x_2967_ = l_Lean_Syntax_node6(v___x_2873_, v___x_2875_, v___x_2876_, v___x_2880_, v___x_2880_, v___x_2913_, v___x_2915_, v___x_2966_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2967_);
v___x_2969_ = v___x_2866_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_toCold_2973_; lean_object* v_ref_2974_; lean_object* v_quotContext_2975_; lean_object* v_currMacroScope_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_dec(v_ctorIdxName_2856_);
v_toCold_2973_ = lean_ctor_get(v_a_2828_, 0);
v_ref_2974_ = lean_ctor_get(v_a_2828_, 2);
v_quotContext_2975_ = lean_ctor_get(v_toCold_2973_, 8);
v_currMacroScope_2976_ = lean_ctor_get(v_toCold_2973_, 9);
v___x_2977_ = 0;
v___x_2978_ = l_Lean_SourceInfo_fromRef(v_ref_2974_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2980_ = l_Lean_mkCIdent(v_a_2860_);
v___x_2981_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2982_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34);
v___x_2983_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35));
lean_inc(v_currMacroScope_2976_);
lean_inc(v_quotContext_2975_);
v___x_2984_ = l_Lean_addMacroScope(v_quotContext_2975_, v___x_2983_, v_currMacroScope_2976_);
v___x_2985_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37));
lean_inc(v___x_2978_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 3);
lean_ctor_set(v___x_2833_, 3, v___x_2985_);
lean_ctor_set(v___x_2833_, 2, v___x_2984_);
lean_ctor_set(v___x_2833_, 1, v___x_2982_);
lean_ctor_set(v___x_2833_, 0, v___x_2978_);
v___x_2987_ = v___x_2833_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2988_ = l_Array_mkArray3___redArg(v_x1_2850_, v_x2_2853_, v___x_2987_);
v___x_2989_ = l_Array_append___redArg(v___x_2988_, v_a_2864_);
lean_dec(v_a_2864_);
lean_inc(v___x_2978_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 1);
lean_ctor_set(v___x_2844_, 2, v___x_2989_);
lean_ctor_set(v___x_2844_, 1, v___x_2981_);
lean_ctor_set(v___x_2844_, 0, v___x_2978_);
v___x_2991_ = v___x_2844_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2992_ = l_Lean_Syntax_node2(v___x_2978_, v___x_2979_, v___x_2980_, v___x_2991_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2992_);
v___x_2994_ = v___x_2866_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v___x_2862_);
lean_dec(v_a_2860_);
lean_dec(v_ctorIdxName_2856_);
lean_dec(v_x2_2853_);
lean_dec(v_x1_2850_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2833_);
v_a_2999_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2863_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2863_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2860_);
lean_dec(v_ctorIdxName_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v_x2_2853_);
lean_dec(v_x1_2850_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2833_);
lean_dec_ref(v_indVal_2822_);
v_a_3007_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2861_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2861_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
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
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_ctorIdxName_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v_x2_2853_);
lean_dec(v_x1_2850_);
lean_del_object(v___x_2844_);
lean_dec(v_name_2842_);
lean_del_object(v___x_2833_);
lean_dec_ref(v_indVal_2822_);
v_a_3015_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2859_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2859_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object* v_header_3030_, lean_object* v_indVal_3031_, lean_object* v_auxFunName_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3030_, v_indVal_3031_, v_auxFunName_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object* v___x_3041_, lean_object* v_as_3042_, size_t v_i_3043_, size_t v_stop_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_3041_, v_as_3042_, v_i_3043_, v_stop_3044_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object* v___x_3053_, lean_object* v_as_3054_, lean_object* v_i_3055_, lean_object* v_stop_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
size_t v_i_boxed_3064_; size_t v_stop_boxed_3065_; lean_object* v_res_3066_; 
v_i_boxed_3064_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_stop_boxed_3065_ = lean_unbox_usize(v_stop_3056_);
lean_dec(v_stop_3056_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(v___x_3053_, v_as_3054_, v_i_boxed_3064_, v_stop_boxed_3065_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v_as_3054_);
lean_dec(v___x_3053_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object* v_upperBound_3067_, lean_object* v_indVal_3068_, lean_object* v___x_3069_, lean_object* v_xs_3070_, lean_object* v_a_3071_, lean_object* v___x_3072_, lean_object* v_auxFunName_3073_, lean_object* v_inst_3074_, lean_object* v_R_3075_, lean_object* v_a_3076_, lean_object* v_b_3077_, lean_object* v_c_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_3067_, v_indVal_3068_, v___x_3069_, v_xs_3070_, v_a_3071_, v___x_3072_, v_auxFunName_3073_, v_a_3076_, v_b_3077_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_3087_ = _args[0];
lean_object* v_indVal_3088_ = _args[1];
lean_object* v___x_3089_ = _args[2];
lean_object* v_xs_3090_ = _args[3];
lean_object* v_a_3091_ = _args[4];
lean_object* v___x_3092_ = _args[5];
lean_object* v_auxFunName_3093_ = _args[6];
lean_object* v_inst_3094_ = _args[7];
lean_object* v_R_3095_ = _args[8];
lean_object* v_a_3096_ = _args[9];
lean_object* v_b_3097_ = _args[10];
lean_object* v_c_3098_ = _args[11];
lean_object* v___y_3099_ = _args[12];
lean_object* v___y_3100_ = _args[13];
lean_object* v___y_3101_ = _args[14];
lean_object* v___y_3102_ = _args[15];
lean_object* v___y_3103_ = _args[16];
lean_object* v___y_3104_ = _args[17];
lean_object* v___y_3105_ = _args[18];
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(v_upperBound_3087_, v_indVal_3088_, v___x_3089_, v_xs_3090_, v_a_3091_, v___x_3092_, v_auxFunName_3093_, v_inst_3094_, v_R_3095_, v_a_3096_, v_b_3097_, v_c_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___x_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v___x_3089_);
lean_dec_ref(v_indVal_3088_);
lean_dec(v_upperBound_3087_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object* v_00_u03b1_3107_, lean_object* v_n_3108_, lean_object* v_f_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_3108_, v_f_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_n_3119_, lean_object* v_f_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(v_00_u03b1_3118_, v_n_3119_, v_f_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v_n_3119_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object* v_00_u03b1_3129_, lean_object* v_f_3130_, lean_object* v_n_3131_, lean_object* v_x_3132_, lean_object* v_i_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_3130_, v_n_3131_, v_x_3132_, v_i_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3142_, lean_object* v_f_3143_, lean_object* v_n_3144_, lean_object* v_x_3145_, lean_object* v_i_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(v_00_u03b1_3142_, v_f_3143_, v_n_3144_, v_x_3145_, v_i_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v_n_3144_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object* v_opts_3155_, lean_object* v_opt_3156_){
_start:
{
lean_object* v_name_3157_; lean_object* v_defValue_3158_; lean_object* v_map_3159_; lean_object* v___x_3160_; 
v_name_3157_ = lean_ctor_get(v_opt_3156_, 0);
v_defValue_3158_ = lean_ctor_get(v_opt_3156_, 1);
v_map_3159_ = lean_ctor_get(v_opts_3155_, 0);
v___x_3160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3159_, v_name_3157_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_inc(v_defValue_3158_);
return v_defValue_3158_;
}
else
{
lean_object* v_val_3161_; 
v_val_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_val_3161_);
lean_dec_ref_known(v___x_3160_, 1);
if (lean_obj_tag(v_val_3161_) == 3)
{
lean_object* v_v_3162_; 
v_v_3162_ = lean_ctor_get(v_val_3161_, 0);
lean_inc(v_v_3162_);
lean_dec_ref_known(v_val_3161_, 1);
return v_v_3162_;
}
else
{
lean_dec(v_val_3161_);
lean_inc(v_defValue_3158_);
return v_defValue_3158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object* v_opts_3163_, lean_object* v_opt_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_opts_3163_, v_opt_3164_);
lean_dec_ref(v_opt_3164_);
lean_dec_ref(v_opts_3163_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object* v_header_3166_, lean_object* v_indVal_3167_, lean_object* v_auxFunName_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3176_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3173_);
v___x_3177_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
v___x_3178_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v___x_3176_, v___x_3177_);
lean_dec_ref(v___x_3176_);
v___x_3179_ = l_Lean_InductiveVal_numCtors(v_indVal_3167_);
v___x_3180_ = lean_nat_dec_le(v___x_3178_, v___x_3179_);
lean_dec(v___x_3179_);
lean_dec(v___x_3178_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
v___x_3181_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_3166_, v_indVal_3167_, v_auxFunName_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; 
v___x_3182_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3166_, v_indVal_3167_, v_auxFunName_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object* v_header_3183_, lean_object* v_indVal_3184_, lean_object* v_auxFunName_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_header_3183_, v_indVal_3184_, v_auxFunName_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
return v_res_3193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4));
v___x_3233_ = l_String_toRawSubstring_x27(v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object* v_ctx_3270_, lean_object* v_i_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_typeInfos_3279_; lean_object* v_auxFunNames_3280_; uint8_t v_usePartial_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v_auxFunName_3284_; lean_object* v_indVal_3285_; lean_object* v___x_3286_; 
v_typeInfos_3279_ = lean_ctor_get(v_ctx_3270_, 1);
v_auxFunNames_3280_ = lean_ctor_get(v_ctx_3270_, 2);
v_usePartial_3281_ = lean_ctor_get_uint8(v_ctx_3270_, sizeof(void*)*3);
v___x_3282_ = lean_box(0);
v___x_3283_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_3284_ = lean_array_get_borrowed(v___x_3282_, v_auxFunNames_3280_, v_i_3271_);
v_indVal_3285_ = lean_array_get_borrowed(v___x_3283_, v_typeInfos_3279_, v_i_3271_);
lean_inc(v_indVal_3285_);
v___x_3286_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_3285_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3421_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3421_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3421_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v_body_3292_; lean_object* v___y_3293_; lean_object* v___x_3404_; 
lean_inc(v_auxFunName_3284_);
lean_inc(v_indVal_3285_);
lean_inc(v_a_3287_);
v___x_3404_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_a_3287_, v_indVal_3285_, v_auxFunName_3284_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3404_) == 0)
{
if (v_usePartial_3281_ == 0)
{
lean_object* v_a_3405_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v_body_3292_ = v_a_3405_;
v___y_3293_ = v_a_3276_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3406_; lean_object* v_argNames_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3406_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3404_, 1);
v_argNames_3407_ = lean_ctor_get(v_a_3287_, 1);
v___x_3408_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
lean_inc_ref(v_argNames_3407_);
v___x_3409_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_3270_, v___x_3408_, v_argNames_3407_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v___x_3411_ = l_Lean_Elab_Deriving_mkLet(v_a_3410_, v_a_3406_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v_body_3292_ = v_a_3412_;
v___y_3293_ = v_a_3276_;
goto v___jp_3291_;
}
else
{
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
return v___x_3411_;
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_a_3406_);
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
v_a_3413_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3409_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3409_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
else
{
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
return v___x_3404_;
}
v___jp_3291_:
{
if (v_usePartial_3281_ == 0)
{
lean_object* v_toCold_3294_; lean_object* v_binders_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3342_; 
v_toCold_3294_ = lean_ctor_get(v___y_3293_, 0);
v_binders_3295_ = lean_ctor_get(v_a_3287_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3343_ = lean_ctor_get(v_a_3287_, 3);
lean_dec(v_unused_3343_);
v_unused_3344_ = lean_ctor_get(v_a_3287_, 2);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_a_3287_, 1);
lean_dec(v_unused_3345_);
v___x_3297_ = v_a_3287_;
v_isShared_3298_ = v_isSharedCheck_3342_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_binders_3295_);
lean_dec(v_a_3287_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3342_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_ref_3299_; lean_object* v_quotContext_3300_; lean_object* v_currMacroScope_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v_ref_3299_ = lean_ctor_get(v___y_3293_, 2);
v_quotContext_3300_ = lean_ctor_get(v_toCold_3294_, 8);
v_currMacroScope_3301_ = lean_ctor_get(v_toCold_3294_, 9);
v___x_3302_ = l_Lean_SourceInfo_fromRef(v_ref_3299_, v_usePartial_3281_);
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3304_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3306_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3302_, 7);
v___x_3307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3302_);
lean_ctor_set(v___x_3307_, 1, v___x_3305_);
lean_ctor_set(v___x_3307_, 2, v___x_3306_);
lean_inc_ref_n(v___x_3307_, 8);
v___x_3308_ = l_Lean_Syntax_node7(v___x_3302_, v___x_3304_, v___x_3307_, v___x_3307_, v___x_3307_, v___x_3307_, v___x_3307_, v___x_3307_, v___x_3307_);
v___x_3309_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3310_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3302_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3284_);
v___x_3313_ = l_Lean_mkIdent(v_auxFunName_3284_);
v___x_3314_ = l_Lean_Syntax_node2(v___x_3302_, v___x_3312_, v___x_3313_, v___x_3307_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3316_ = l_Array_append___redArg(v___x_3306_, v_binders_3295_);
lean_dec_ref(v_binders_3295_);
v___x_3317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3302_);
lean_ctor_set(v___x_3317_, 1, v___x_3305_);
lean_ctor_set(v___x_3317_, 2, v___x_3316_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3302_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3301_);
lean_inc(v_quotContext_3300_);
v___x_3323_ = l_Lean_addMacroScope(v_quotContext_3300_, v___x_3322_, v_currMacroScope_3301_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 3);
lean_ctor_set(v___x_3297_, 3, v___x_3324_);
lean_ctor_set(v___x_3297_, 2, v___x_3323_);
lean_ctor_set(v___x_3297_, 1, v___x_3321_);
lean_ctor_set(v___x_3297_, 0, v___x_3302_);
v___x_3326_ = v___x_3297_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3302_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_inc_n(v___x_3302_, 7);
v___x_3327_ = l_Lean_Syntax_node2(v___x_3302_, v___x_3318_, v___x_3320_, v___x_3326_);
v___x_3328_ = l_Lean_Syntax_node1(v___x_3302_, v___x_3305_, v___x_3327_);
v___x_3329_ = l_Lean_Syntax_node2(v___x_3302_, v___x_3315_, v___x_3317_, v___x_3328_);
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3302_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3307_, 3);
v___x_3334_ = l_Lean_Syntax_node2(v___x_3302_, v___x_3333_, v___x_3307_, v___x_3307_);
v___x_3335_ = l_Lean_Syntax_node4(v___x_3302_, v___x_3330_, v___x_3332_, v_body_3292_, v___x_3334_, v___x_3307_);
v___x_3336_ = l_Lean_Syntax_node5(v___x_3302_, v___x_3309_, v___x_3311_, v___x_3314_, v___x_3329_, v___x_3335_, v___x_3307_);
v___x_3337_ = l_Lean_Syntax_node2(v___x_3302_, v___x_3303_, v___x_3308_, v___x_3336_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3337_);
v___x_3339_ = v___x_3289_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_toCold_3346_; lean_object* v_binders_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3400_; 
v_toCold_3346_ = lean_ctor_get(v___y_3293_, 0);
v_binders_3347_ = lean_ctor_get(v_a_3287_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; 
v_unused_3401_ = lean_ctor_get(v_a_3287_, 3);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_a_3287_, 2);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_a_3287_, 1);
lean_dec(v_unused_3403_);
v___x_3349_ = v_a_3287_;
v_isShared_3350_ = v_isSharedCheck_3400_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_binders_3347_);
lean_dec(v_a_3287_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3400_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_ref_3351_; lean_object* v_quotContext_3352_; lean_object* v_currMacroScope_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3384_; 
v_ref_3351_ = lean_ctor_get(v___y_3293_, 2);
v_quotContext_3352_ = lean_ctor_get(v_toCold_3346_, 8);
v_currMacroScope_3353_ = lean_ctor_get(v_toCold_3346_, 9);
v___x_3354_ = 0;
v___x_3355_ = l_Lean_SourceInfo_fromRef(v_ref_3351_, v___x_3354_);
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3359_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3355_, 10);
v___x_3360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3355_);
lean_ctor_set(v___x_3360_, 1, v___x_3358_);
lean_ctor_set(v___x_3360_, 2, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27));
v___x_3362_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28));
v___x_3363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3355_);
lean_ctor_set(v___x_3363_, 1, v___x_3361_);
v___x_3364_ = l_Lean_Syntax_node1(v___x_3355_, v___x_3362_, v___x_3363_);
v___x_3365_ = l_Lean_Syntax_node1(v___x_3355_, v___x_3358_, v___x_3364_);
lean_inc_ref_n(v___x_3360_, 7);
v___x_3366_ = l_Lean_Syntax_node7(v___x_3355_, v___x_3357_, v___x_3360_, v___x_3360_, v___x_3360_, v___x_3360_, v___x_3360_, v___x_3360_, v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3355_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3284_);
v___x_3371_ = l_Lean_mkIdent(v_auxFunName_3284_);
v___x_3372_ = l_Lean_Syntax_node2(v___x_3355_, v___x_3370_, v___x_3371_, v___x_3360_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3374_ = l_Array_append___redArg(v___x_3359_, v_binders_3347_);
lean_dec_ref(v_binders_3347_);
v___x_3375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3355_);
lean_ctor_set(v___x_3375_, 1, v___x_3358_);
lean_ctor_set(v___x_3375_, 2, v___x_3374_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3377_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3355_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3380_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3353_);
lean_inc(v_quotContext_3352_);
v___x_3381_ = l_Lean_addMacroScope(v_quotContext_3352_, v___x_3380_, v_currMacroScope_3353_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 3);
lean_ctor_set(v___x_3349_, 3, v___x_3382_);
lean_ctor_set(v___x_3349_, 2, v___x_3381_);
lean_ctor_set(v___x_3349_, 1, v___x_3379_);
lean_ctor_set(v___x_3349_, 0, v___x_3355_);
v___x_3384_ = v___x_3349_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3399_, 3, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
lean_inc_n(v___x_3355_, 7);
v___x_3385_ = l_Lean_Syntax_node2(v___x_3355_, v___x_3376_, v___x_3378_, v___x_3384_);
v___x_3386_ = l_Lean_Syntax_node1(v___x_3355_, v___x_3358_, v___x_3385_);
v___x_3387_ = l_Lean_Syntax_node2(v___x_3355_, v___x_3373_, v___x_3375_, v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3355_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3360_, 3);
v___x_3392_ = l_Lean_Syntax_node2(v___x_3355_, v___x_3391_, v___x_3360_, v___x_3360_);
v___x_3393_ = l_Lean_Syntax_node4(v___x_3355_, v___x_3388_, v___x_3390_, v_body_3292_, v___x_3392_, v___x_3360_);
v___x_3394_ = l_Lean_Syntax_node5(v___x_3355_, v___x_3367_, v___x_3369_, v___x_3372_, v___x_3387_, v___x_3393_, v___x_3360_);
v___x_3395_ = l_Lean_Syntax_node2(v___x_3355_, v___x_3356_, v___x_3366_, v___x_3394_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3395_);
v___x_3397_ = v___x_3289_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
v_a_3422_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3286_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3286_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object* v_ctx_3430_, lean_object* v_i_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3430_, v_i_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_i_3431_);
lean_dec_ref(v_ctx_3430_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_3440_, lean_object* v_ctx_3441_, lean_object* v_a_3442_, lean_object* v_b_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_nat_dec_lt(v_a_3442_, v_upperBound_3440_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec(v_a_3442_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3443_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3441_, v_a_3442_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = lean_array_push(v_b_3443_, v_a_3454_);
v___x_3456_ = lean_unsigned_to_nat(1u);
v___x_3457_ = lean_nat_add(v_a_3442_, v___x_3456_);
lean_dec(v_a_3442_);
v_a_3442_ = v___x_3457_;
v_b_3443_ = v___x_3455_;
goto _start;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_b_3443_);
lean_dec(v_a_3442_);
v_a_3459_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3453_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3453_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_3467_, lean_object* v_ctx_3468_, lean_object* v_a_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3467_, v_ctx_3468_, v_a_3469_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v_ctx_3468_);
lean_dec(v_upperBound_3467_);
return v_res_3478_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4));
v___x_3493_ = l_String_toRawSubstring_x27(v___x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object* v_ctx_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_typeInfos_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_auxDefs_3519_; lean_object* v___x_3520_; 
v_typeInfos_3516_ = lean_ctor_get(v_ctx_3508_, 1);
v___x_3517_ = lean_array_get_size(v_typeInfos_3516_);
v___x_3518_ = lean_unsigned_to_nat(0u);
v_auxDefs_3519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_3520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v___x_3517_, v_ctx_3508_, v___x_3518_, v_auxDefs_3519_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_toCold_3521_; lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3557_; 
v_toCold_3521_ = lean_ctor_get(v_a_3513_, 0);
v_a_3522_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3524_ = v___x_3520_;
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_ref_3526_; lean_object* v_quotContext_3527_; lean_object* v_currMacroScope_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v_ref_3526_ = lean_ctor_get(v_a_3513_, 2);
v_quotContext_3527_ = lean_ctor_get(v_toCold_3521_, 8);
v_currMacroScope_3528_ = lean_ctor_get(v_toCold_3521_, 9);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_SourceInfo_fromRef(v_ref_3526_, v___x_3529_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0));
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1));
lean_inc_n(v___x_3530_, 8);
v___x_3533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3530_);
lean_ctor_set(v___x_3533_, 1, v___x_3531_);
v___x_3534_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3535_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2));
v___x_3536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3));
v___x_3537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3530_);
lean_ctor_set(v___x_3537_, 1, v___x_3535_);
v___x_3538_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5);
v___x_3539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_3528_);
lean_inc(v_quotContext_3527_);
v___x_3540_ = l_Lean_addMacroScope(v_quotContext_3527_, v___x_3539_, v_currMacroScope_3528_);
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10));
v___x_3542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3530_);
lean_ctor_set(v___x_3542_, 1, v___x_3538_);
lean_ctor_set(v___x_3542_, 2, v___x_3540_);
lean_ctor_set(v___x_3542_, 3, v___x_3541_);
v___x_3543_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_3544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3530_);
lean_ctor_set(v___x_3544_, 1, v___x_3534_);
lean_ctor_set(v___x_3544_, 2, v___x_3543_);
v___x_3545_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_3546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3530_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_Syntax_node4(v___x_3530_, v___x_3536_, v___x_3537_, v___x_3542_, v___x_3544_, v___x_3546_);
v___x_3548_ = l_Array_mkArray1___redArg(v___x_3547_);
v___x_3549_ = l_Array_append___redArg(v___x_3548_, v_a_3522_);
lean_dec(v_a_3522_);
v___x_3550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3530_);
lean_ctor_set(v___x_3550_, 1, v___x_3534_);
lean_ctor_set(v___x_3550_, 2, v___x_3549_);
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11));
v___x_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3530_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_Syntax_node3(v___x_3530_, v___x_3532_, v___x_3533_, v___x_3550_, v___x_3552_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3553_);
v___x_3555_ = v___x_3524_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_a_3558_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3520_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3520_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object* v_ctx_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec_ref(v_ctx_3566_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object* v_upperBound_3575_, lean_object* v_ctx_3576_, lean_object* v_inst_3577_, lean_object* v_R_3578_, lean_object* v_a_3579_, lean_object* v_b_3580_, lean_object* v_c_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3575_, v_ctx_3576_, v_a_3579_, v_b_3580_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_3590_, lean_object* v_ctx_3591_, lean_object* v_inst_3592_, lean_object* v_R_3593_, lean_object* v_a_3594_, lean_object* v_b_3595_, lean_object* v_c_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(v_upperBound_3590_, v_ctx_3591_, v_inst_3592_, v_R_3593_, v_a_3594_, v_b_3595_, v_c_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_ctx_3591_);
lean_dec(v_upperBound_3590_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
if (lean_obj_tag(v_a_3605_) == 0)
{
lean_object* v___x_3607_; 
v___x_3607_ = l_List_reverse___redArg(v_a_3606_);
return v___x_3607_;
}
else
{
lean_object* v_head_3608_; lean_object* v_tail_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3618_; 
v_head_3608_ = lean_ctor_get(v_a_3605_, 0);
v_tail_3609_ = lean_ctor_get(v_a_3605_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_a_3605_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3611_ = v_a_3605_;
v_isShared_3612_ = v_isSharedCheck_3618_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_tail_3609_);
lean_inc(v_head_3608_);
lean_dec(v_a_3605_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3618_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = l_Lean_MessageData_ofSyntax(v_head_3608_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 1, v_a_3606_);
lean_ctor_set(v___x_3611_, 0, v___x_3613_);
v___x_3615_ = v___x_3611_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3606_);
v___x_3615_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
v_a_3605_ = v_tail_3609_;
v_a_3606_ = v___x_3615_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3619_; double v___x_3620_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = lean_float_of_nat(v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object* v_cls_3623_, lean_object* v_msg_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_ref_3630_; lean_object* v___x_3631_; lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3677_; 
v_ref_3630_ = lean_ctor_get(v___y_3627_, 2);
v___x_3631_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3677_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3677_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v_traceState_3637_; lean_object* v_env_3638_; lean_object* v_nextMacroScope_3639_; lean_object* v_ngen_3640_; lean_object* v_auxDeclNGen_3641_; lean_object* v_cache_3642_; lean_object* v_recordedDeps_3643_; lean_object* v_messages_3644_; lean_object* v_infoState_3645_; lean_object* v_snapshotTasks_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3676_; 
v___x_3636_ = lean_st_ref_take(v___y_3628_);
v_traceState_3637_ = lean_ctor_get(v___x_3636_, 4);
v_env_3638_ = lean_ctor_get(v___x_3636_, 0);
v_nextMacroScope_3639_ = lean_ctor_get(v___x_3636_, 1);
v_ngen_3640_ = lean_ctor_get(v___x_3636_, 2);
v_auxDeclNGen_3641_ = lean_ctor_get(v___x_3636_, 3);
v_cache_3642_ = lean_ctor_get(v___x_3636_, 5);
v_recordedDeps_3643_ = lean_ctor_get(v___x_3636_, 6);
v_messages_3644_ = lean_ctor_get(v___x_3636_, 7);
v_infoState_3645_ = lean_ctor_get(v___x_3636_, 8);
v_snapshotTasks_3646_ = lean_ctor_get(v___x_3636_, 9);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3648_ = v___x_3636_;
v_isShared_3649_ = v_isSharedCheck_3676_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_snapshotTasks_3646_);
lean_inc(v_infoState_3645_);
lean_inc(v_messages_3644_);
lean_inc(v_recordedDeps_3643_);
lean_inc(v_cache_3642_);
lean_inc(v_traceState_3637_);
lean_inc(v_auxDeclNGen_3641_);
lean_inc(v_ngen_3640_);
lean_inc(v_nextMacroScope_3639_);
lean_inc(v_env_3638_);
lean_dec(v___x_3636_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3676_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
uint64_t v_tid_3650_; lean_object* v_traces_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3675_; 
v_tid_3650_ = lean_ctor_get_uint64(v_traceState_3637_, sizeof(void*)*1);
v_traces_3651_ = lean_ctor_get(v_traceState_3637_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_traceState_3637_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3653_ = v_traceState_3637_;
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_traces_3651_);
lean_dec(v_traceState_3637_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; double v___x_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3655_ = lean_box(0);
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0);
v___x_3658_ = 0;
v___x_3659_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_3660_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3660_, 0, v_cls_3623_);
lean_ctor_set(v___x_3660_, 1, v___x_3656_);
lean_ctor_set(v___x_3660_, 2, v___x_3659_);
lean_ctor_set_float(v___x_3660_, sizeof(void*)*3, v___x_3657_);
lean_ctor_set_float(v___x_3660_, sizeof(void*)*3 + 8, v___x_3657_);
lean_ctor_set_uint8(v___x_3660_, sizeof(void*)*3 + 16, v___x_3658_);
v___x_3661_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1));
v___x_3662_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v_a_3632_);
lean_ctor_set(v___x_3662_, 2, v___x_3661_);
lean_inc(v_ref_3630_);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_ref_3630_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_PersistentArray_push___redArg(v_traces_3651_, v___x_3663_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3664_);
v___x_3666_ = v___x_3653_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3664_);
lean_ctor_set_uint64(v_reuseFailAlloc_3674_, sizeof(void*)*1, v_tid_3650_);
v___x_3666_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v___x_3666_);
v___x_3668_ = v___x_3648_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_env_3638_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_nextMacroScope_3639_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_ngen_3640_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_auxDeclNGen_3641_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3673_, 5, v_cache_3642_);
lean_ctor_set(v_reuseFailAlloc_3673_, 6, v_recordedDeps_3643_);
lean_ctor_set(v_reuseFailAlloc_3673_, 7, v_messages_3644_);
lean_ctor_set(v_reuseFailAlloc_3673_, 8, v_infoState_3645_);
lean_ctor_set(v_reuseFailAlloc_3673_, 9, v_snapshotTasks_3646_);
v___x_3668_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3669_ = lean_st_ref_put(v___y_3628_, v___x_3668_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3655_);
v___x_3671_ = v___x_3634_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3655_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3678_, lean_object* v_msg_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3678_, v_msg_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
return v_res_3685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2));
v___x_3695_ = l_Lean_Name_append(v___x_3694_, v___x_3693_);
return v___x_3695_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4));
v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object* v_ctx_3699_, lean_object* v_declName_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3699_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; lean_object* v___x_3715_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3712_ = lean_mk_empty_array_with_capacity(v___x_3711_);
lean_inc_ref(v___x_3712_);
v___x_3713_ = lean_array_push(v___x_3712_, v_declName_3700_);
v___x_3714_ = 1;
v___x_3715_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3699_, v___x_3710_, v___x_3713_, v___x_3714_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
lean_dec_ref(v___x_3713_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_toCold_3716_; lean_object* v_options_3717_; lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3758_; 
v_toCold_3716_ = lean_ctor_get(v_a_3705_, 0);
v_options_3717_ = lean_ctor_get(v_toCold_3716_, 2);
v_a_3718_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3720_ = v___x_3715_;
v_isShared_3721_ = v_isSharedCheck_3758_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3715_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3758_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_inheritedTraceOptions_3722_; uint8_t v_hasTrace_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_inheritedTraceOptions_3722_ = lean_ctor_get(v_toCold_3716_, 11);
v_hasTrace_3723_ = lean_ctor_get_uint8(v_options_3717_, sizeof(void*)*1);
v___x_3724_ = lean_array_push(v___x_3712_, v_a_3709_);
v___x_3725_ = l_Array_append___redArg(v___x_3724_, v_a_3718_);
lean_dec(v_a_3718_);
if (v_hasTrace_3723_ == 0)
{
lean_object* v___x_3727_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3725_);
v___x_3727_ = v___x_3720_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3729_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3730_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3722_, v_options_3717_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3733_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3725_);
v___x_3733_ = v___x_3720_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3725_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_del_object(v___x_3720_);
v___x_3735_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3725_);
v___x_3736_ = lean_array_to_list(v___x_3725_);
v___x_3737_ = lean_box(0);
v___x_3738_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3736_, v___x_3737_);
v___x_3739_ = l_Lean_MessageData_ofList(v___x_3738_);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3735_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3729_, v___x_3740_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3749_);
v___x_3743_ = v___x_3741_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3725_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3725_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v___x_3725_);
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v___x_3712_);
lean_dec(v_a_3709_);
v_a_3759_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3715_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3715_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_declName_3700_);
lean_dec_ref(v_ctx_3699_);
v_a_3767_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3708_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3708_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object* v_ctx_3775_, lean_object* v_declName_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_ctx_3775_, v_declName_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object* v_cls_3785_, lean_object* v_msg_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3785_, v_msg_3786_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object* v_cls_3795_, lean_object* v_msg_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(v_cls_3795_, v_msg_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3804_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2));
v___x_3813_ = l_String_toRawSubstring_x27(v___x_3812_);
return v___x_3813_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5));
v___x_3818_ = l_String_toRawSubstring_x27(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11));
v___x_3832_ = l_String_toRawSubstring_x27(v___x_3831_);
return v___x_3832_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15));
v___x_3839_ = l_String_toRawSubstring_x27(v___x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object* v_ctx_3843_, lean_object* v_name_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v_toCold_3847_; lean_object* v_auxFunNames_3848_; lean_object* v_ref_3849_; lean_object* v_quotContext_3850_; lean_object* v_currMacroScope_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v_auxFunName_3854_; uint8_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_toCold_3847_ = lean_ctor_get(v_a_3845_, 0);
v_auxFunNames_3848_ = lean_ctor_get(v_ctx_3843_, 2);
v_ref_3849_ = lean_ctor_get(v_a_3845_, 2);
v_quotContext_3850_ = lean_ctor_get(v_toCold_3847_, 8);
v_currMacroScope_3851_ = lean_ctor_get(v_toCold_3847_, 9);
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_unsigned_to_nat(0u);
v_auxFunName_3854_ = lean_array_get_borrowed(v___x_3852_, v_auxFunNames_3848_, v___x_3853_);
v___x_3855_ = 0;
v___x_3856_ = l_Lean_SourceInfo_fromRef(v_ref_3849_, v___x_3855_);
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3858_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3860_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3856_, 25);
v___x_3861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3856_);
lean_ctor_set(v___x_3861_, 1, v___x_3859_);
lean_ctor_set(v___x_3861_, 2, v___x_3860_);
lean_inc_ref_n(v___x_3861_, 12);
v___x_3862_ = l_Lean_Syntax_node7(v___x_3856_, v___x_3858_, v___x_3861_, v___x_3861_, v___x_3861_, v___x_3861_, v___x_3861_, v___x_3861_, v___x_3861_);
v___x_3863_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3864_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3856_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3854_);
v___x_3867_ = l_Lean_mkIdent(v_auxFunName_3854_);
v___x_3868_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3866_, v___x_3867_, v___x_3861_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1));
v___x_3871_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_3872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3856_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3);
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3851_, 5);
lean_inc_n(v_quotContext_3850_, 5);
v___x_3875_ = l_Lean_addMacroScope(v_quotContext_3850_, v___x_3874_, v_currMacroScope_3851_);
v___x_3876_ = lean_box(0);
v___x_3877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3856_);
lean_ctor_set(v___x_3877_, 1, v___x_3873_);
lean_ctor_set(v___x_3877_, 2, v___x_3875_);
lean_ctor_set(v___x_3877_, 3, v___x_3876_);
v___x_3878_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6);
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7));
v___x_3880_ = l_Lean_addMacroScope(v_quotContext_3850_, v___x_3879_, v_currMacroScope_3851_);
v___x_3881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3856_);
lean_ctor_set(v___x_3881_, 1, v___x_3878_);
lean_ctor_set(v___x_3881_, 2, v___x_3880_);
lean_ctor_set(v___x_3881_, 3, v___x_3876_);
v___x_3882_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3859_, v___x_3877_, v___x_3881_);
v___x_3883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3856_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = l_Lean_mkCIdent(v_name_3844_);
lean_inc_ref(v___x_3884_);
v___x_3886_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3859_, v___x_3884_, v___x_3885_);
v___x_3887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_3888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3856_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_Syntax_node5(v___x_3856_, v___x_3870_, v___x_3872_, v___x_3882_, v___x_3886_, v___x_3861_, v___x_3888_);
v___x_3890_ = l_Lean_Syntax_node1(v___x_3856_, v___x_3859_, v___x_3889_);
v___x_3891_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3892_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3893_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
v___x_3894_ = l_Lean_addMacroScope(v_quotContext_3850_, v___x_3893_, v_currMacroScope_3851_);
v___x_3895_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10));
v___x_3896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3856_);
lean_ctor_set(v___x_3896_, 1, v___x_3892_);
lean_ctor_set(v___x_3896_, 2, v___x_3894_);
lean_ctor_set(v___x_3896_, 3, v___x_3895_);
v___x_3897_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3891_, v___x_3884_, v___x_3896_);
v___x_3898_ = l_Lean_Syntax_node1(v___x_3856_, v___x_3859_, v___x_3897_);
v___x_3899_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3869_, v___x_3890_, v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3856_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_3904_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12);
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14));
v___x_3906_ = l_Lean_addMacroScope(v_quotContext_3850_, v___x_3905_, v_currMacroScope_3851_);
v___x_3907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3856_);
lean_ctor_set(v___x_3907_, 1, v___x_3904_);
lean_ctor_set(v___x_3907_, 2, v___x_3906_);
lean_ctor_set(v___x_3907_, 3, v___x_3876_);
v___x_3908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_3909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3856_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16);
v___x_3911_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17));
v___x_3912_ = l_Lean_addMacroScope(v_quotContext_3850_, v___x_3911_, v_currMacroScope_3851_);
v___x_3913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3856_);
lean_ctor_set(v___x_3913_, 1, v___x_3910_);
lean_ctor_set(v___x_3913_, 2, v___x_3912_);
lean_ctor_set(v___x_3913_, 3, v___x_3876_);
v___x_3914_ = l_Lean_Syntax_node3(v___x_3856_, v___x_3903_, v___x_3907_, v___x_3909_, v___x_3913_);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
v___x_3916_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3915_, v___x_3861_, v___x_3861_);
v___x_3917_ = l_Lean_Syntax_node4(v___x_3856_, v___x_3900_, v___x_3902_, v___x_3914_, v___x_3916_, v___x_3861_);
v___x_3918_ = l_Lean_Syntax_node5(v___x_3856_, v___x_3863_, v___x_3865_, v___x_3868_, v___x_3899_, v___x_3917_, v___x_3861_);
v___x_3919_ = l_Lean_Syntax_node2(v___x_3856_, v___x_3857_, v___x_3862_, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object* v_ctx_3921_, lean_object* v_name_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3921_, v_name_3922_, v_a_3923_);
lean_dec_ref(v_a_3923_);
lean_dec_ref(v_ctx_3921_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object* v_ctx_3926_, lean_object* v_name_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3926_, v_name_3927_, v_a_3932_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object* v_ctx_3936_, lean_object* v_name_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(v_ctx_3936_, v_name_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec_ref(v_ctx_3936_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object* v_ctx_3946_, lean_object* v_name_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3955_; lean_object* v_a_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; 
lean_inc(v_name_3947_);
v___x_3955_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3946_, v_name_3947_, v_a_3952_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_mk_empty_array_with_capacity(v___x_3958_);
lean_inc_ref(v___x_3959_);
v___x_3960_ = lean_array_push(v___x_3959_, v_name_3947_);
v___x_3961_ = 1;
v___x_3962_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3946_, v___x_3957_, v___x_3960_, v___x_3961_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
lean_dec_ref(v___x_3960_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_toCold_3963_; lean_object* v_options_3964_; lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_4005_; 
v_toCold_3963_ = lean_ctor_get(v_a_3952_, 0);
v_options_3964_ = lean_ctor_get(v_toCold_3963_, 2);
v_a_3965_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3967_ = v___x_3962_;
v_isShared_3968_ = v_isSharedCheck_4005_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3962_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_4005_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v_inheritedTraceOptions_3969_; uint8_t v_hasTrace_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_inheritedTraceOptions_3969_ = lean_ctor_get(v_toCold_3963_, 11);
v_hasTrace_3970_ = lean_ctor_get_uint8(v_options_3964_, sizeof(void*)*1);
v___x_3971_ = lean_array_push(v___x_3959_, v_a_3956_);
v___x_3972_ = l_Array_append___redArg(v___x_3971_, v_a_3965_);
lean_dec(v_a_3965_);
if (v_hasTrace_3970_ == 0)
{
lean_object* v___x_3974_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3972_);
v___x_3974_ = v___x_3967_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3976_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3977_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3969_, v_options_3964_, v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3980_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3972_);
v___x_3980_ = v___x_3967_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3972_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_del_object(v___x_3967_);
v___x_3982_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3972_);
v___x_3983_ = lean_array_to_list(v___x_3972_);
v___x_3984_ = lean_box(0);
v___x_3985_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3983_, v___x_3984_);
v___x_3986_ = l_Lean_MessageData_ofList(v___x_3985_);
v___x_3987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3982_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3976_, v___x_3987_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v___x_3988_, 0);
lean_dec(v_unused_3996_);
v___x_3990_ = v___x_3988_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v___x_3972_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3972_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec_ref(v___x_3972_);
v_a_3997_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3988_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3988_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v___x_3959_);
lean_dec(v_a_3956_);
v_a_4006_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3962_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3962_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object* v_ctx_4014_, lean_object* v_name_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_ctx_4014_, v_name_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; lean_object* v_env_4027_; lean_object* v___x_4028_; lean_object* v_mainModule_4029_; lean_object* v___x_4030_; 
v___x_4026_ = lean_st_ref_get(v___y_4024_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
v___x_4028_ = l_Lean_Environment_header(v_env_4027_);
lean_dec_ref(v_env_4027_);
v_mainModule_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_mainModule_4029_);
lean_dec_ref(v___x_4028_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v_mainModule_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4031_);
lean_dec(v___y_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4035_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t v_a_4042_, lean_object* v_a_4043_, lean_object* v_declName_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
if (v_a_4042_ == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_a_4043_, v_declName_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v___x_4052_;
}
else
{
lean_object* v___x_4053_; 
v___x_4053_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_a_4043_, v_declName_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v___x_4053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_declName_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
uint8_t v_a_6158__boxed_4064_; lean_object* v_res_4065_; 
v_a_6158__boxed_4064_ = lean_unbox(v_a_4054_);
v_res_4065_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(v_a_6158__boxed_4064_, v_a_4055_, v_declName_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4070_ = lean_unsigned_to_nat(0u);
v___x_4071_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
lean_ctor_set(v___x_4071_, 2, v___x_4070_);
lean_ctor_set(v___x_4071_, 3, v___x_4070_);
lean_ctor_set(v___x_4071_, 4, v___x_4069_);
lean_ctor_set(v___x_4071_, 5, v___x_4069_);
lean_ctor_set(v___x_4071_, 6, v___x_4069_);
lean_ctor_set(v___x_4071_, 7, v___x_4069_);
lean_ctor_set(v___x_4071_, 8, v___x_4069_);
lean_ctor_set(v___x_4071_, 9, v___x_4069_);
lean_ctor_set(v___x_4071_, 10, v___x_4069_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = lean_unsigned_to_nat(32u);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4075_ = ((size_t)5ULL);
v___x_4076_ = lean_unsigned_to_nat(0u);
v___x_4077_ = lean_unsigned_to_nat(32u);
v___x_4078_ = lean_mk_empty_array_with_capacity(v___x_4077_);
v___x_4079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_4080_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4078_);
lean_ctor_set(v___x_4080_, 2, v___x_4076_);
lean_ctor_set(v___x_4080_, 3, v___x_4076_);
lean_ctor_set_usize(v___x_4080_, 4, v___x_4075_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4081_ = lean_box(1);
v___x_4082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_4083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
lean_ctor_set(v___x_4084_, 1, v___x_4082_);
lean_ctor_set(v___x_4084_, 2, v___x_4081_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_4087_ = l_Lean_stringToMessageData(v___x_4086_);
return v___x_4087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_4090_ = l_Lean_stringToMessageData(v___x_4089_);
return v___x_4090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_4093_ = l_Lean_stringToMessageData(v___x_4092_);
return v___x_4093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_4096_ = l_Lean_stringToMessageData(v___x_4095_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_4099_ = l_Lean_stringToMessageData(v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_4102_ = l_Lean_stringToMessageData(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_4106_, lean_object* v_declHint_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v_env_4112_; uint8_t v___x_4113_; 
v___x_4110_ = lean_box(0);
v___x_4111_ = lean_st_ref_get(v___y_4108_);
v_env_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_env_4112_);
lean_dec(v___x_4111_);
v___x_4113_ = l_Lean_Name_isAnonymous(v_declHint_4107_);
if (v___x_4113_ == 0)
{
uint8_t v_isExporting_4114_; 
v_isExporting_4114_ = lean_ctor_get_uint8(v_env_4112_, sizeof(void*)*8);
if (v_isExporting_4114_ == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref(v_env_4112_);
lean_dec(v_declHint_4107_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_msg_4106_);
return v___x_4115_;
}
else
{
lean_object* v___x_4116_; uint8_t v___x_4117_; 
lean_inc_ref(v_env_4112_);
v___x_4116_ = l_Lean_Environment_setExporting(v_env_4112_, v___x_4113_);
lean_inc(v_declHint_4107_);
lean_inc_ref(v___x_4116_);
v___x_4117_ = l_Lean_Environment_contains(v___x_4116_, v_declHint_4107_, v_isExporting_4114_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
lean_dec_ref(v___x_4116_);
lean_dec_ref(v_env_4112_);
lean_dec(v_declHint_4107_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_msg_4106_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v_c_4124_; lean_object* v___x_4125_; 
v___x_4119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4121_ = l_Lean_Options_empty;
v___x_4122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4116_);
lean_ctor_set(v___x_4122_, 1, v___x_4119_);
lean_ctor_set(v___x_4122_, 2, v___x_4120_);
lean_ctor_set(v___x_4122_, 3, v___x_4121_);
lean_inc(v_declHint_4107_);
v___x_4123_ = l_Lean_MessageData_ofConstName(v_declHint_4107_, v___x_4113_);
v_c_4124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4124_, 0, v___x_4122_);
lean_ctor_set(v_c_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4112_, v_declHint_4107_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec_ref(v_env_4112_);
lean_dec(v_declHint_4107_);
v___x_4126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v_c_4124_);
v___x_4128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = l_Lean_MessageData_note(v___x_4129_);
v___x_4131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4131_, 0, v_msg_4106_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
else
{
lean_object* v_val_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4167_; 
v_val_4133_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4135_ = v___x_4125_;
v_isShared_4136_ = v_isSharedCheck_4167_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_val_4133_);
lean_dec(v___x_4125_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4167_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v_mod_4139_; uint8_t v___x_4140_; 
v___x_4137_ = l_Lean_Environment_header(v_env_4112_);
lean_dec_ref(v_env_4112_);
v___x_4138_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4137_);
v_mod_4139_ = lean_array_get(v___x_4110_, v___x_4138_, v_val_4133_);
lean_dec(v_val_4133_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = l_Lean_isPrivateName(v_declHint_4107_);
lean_dec(v_declHint_4107_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
lean_ctor_set(v___x_4142_, 1, v_c_4124_);
v___x_4143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = l_Lean_MessageData_ofName(v_mod_4139_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_4148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_MessageData_note(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_msg_4106_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4150_);
v___x_4152_ = v___x_4135_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set(v___x_4155_, 1, v_c_4124_);
v___x_4156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_MessageData_ofName(v_mod_4139_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_MessageData_note(v___x_4161_);
v___x_4163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_msg_4106_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4163_);
v___x_4165_ = v___x_4135_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4168_; 
lean_dec_ref(v_env_4112_);
lean_dec(v_declHint_4107_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_msg_4106_);
return v___x_4168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_4169_, lean_object* v_declHint_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4169_, v_declHint_4170_, v___y_4171_);
lean_dec(v___y_4171_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_4174_, lean_object* v_declHint_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4179_; lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4189_; 
v___x_4179_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4174_, v_declHint_4175_, v___y_4177_);
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4184_ = l_Lean_unknownIdentifierMessageTag;
v___x_4185_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v_a_4180_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4185_);
v___x_4187_ = v___x_4182_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_4190_, lean_object* v_declHint_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4190_, v_declHint_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* v_msgData_4196_, lean_object* v_macroStack_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v_scopes_4202_; lean_object* v___x_4203_; lean_object* v_opts_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4200_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4201_ = lean_st_ref_get(v___y_4198_);
v_scopes_4202_ = lean_ctor_get(v___x_4201_, 2);
lean_inc(v_scopes_4202_);
lean_dec(v___x_4201_);
v___x_4203_ = l_List_head_x21___redArg(v___x_4200_, v_scopes_4202_);
lean_dec(v_scopes_4202_);
v_opts_4204_ = lean_ctor_get(v___x_4203_, 1);
lean_inc_ref(v_opts_4204_);
lean_dec(v___x_4203_);
v___x_4205_ = l_Lean_Elab_pp_macroStack;
v___x_4206_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_4204_, v___x_4205_);
lean_dec_ref(v_opts_4204_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; 
lean_dec(v_macroStack_4197_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_msgData_4196_);
return v___x_4207_;
}
else
{
if (lean_obj_tag(v_macroStack_4197_) == 0)
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_msgData_4196_);
return v___x_4208_;
}
else
{
lean_object* v_head_4209_; lean_object* v_after_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4225_; 
v_head_4209_ = lean_ctor_get(v_macroStack_4197_, 0);
lean_inc(v_head_4209_);
v_after_4210_ = lean_ctor_get(v_head_4209_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_head_4209_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v_head_4209_, 0);
lean_dec(v_unused_4226_);
v___x_4212_ = v_head_4209_;
v_isShared_4213_ = v_isSharedCheck_4225_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_after_4210_);
lean_dec(v_head_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4225_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4214_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_4213_ == 0)
{
lean_ctor_set_tag(v___x_4212_, 7);
lean_ctor_set(v___x_4212_, 1, v___x_4214_);
lean_ctor_set(v___x_4212_, 0, v_msgData_4196_);
v___x_4216_ = v___x_4212_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_msgData_4196_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v_msgData_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4217_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_4218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l_Lean_MessageData_ofSyntax(v_after_4210_);
v___x_4220_ = l_Lean_indentD(v___x_4219_);
v_msgData_4221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4221_, 0, v___x_4218_);
lean_ctor_set(v_msgData_4221_, 1, v___x_4220_);
v___x_4222_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_4221_, v_macroStack_4197_);
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
return v___x_4223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_4227_, lean_object* v_macroStack_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4227_, v_macroStack_4228_, v___y_4229_);
lean_dec(v___y_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object* v_msgData_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; lean_object* v_env_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v_scopes_4239_; lean_object* v___x_4240_; lean_object* v_opts_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4235_ = lean_st_ref_get(v___y_4233_);
v_env_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc_ref(v_env_4236_);
lean_dec(v___x_4235_);
v___x_4237_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4238_ = lean_st_ref_get(v___y_4233_);
v_scopes_4239_ = lean_ctor_get(v___x_4238_, 2);
lean_inc(v_scopes_4239_);
lean_dec(v___x_4238_);
v___x_4240_ = l_List_head_x21___redArg(v___x_4237_, v_scopes_4239_);
lean_dec(v_scopes_4239_);
v_opts_4241_ = lean_ctor_get(v___x_4240_, 1);
lean_inc_ref(v_opts_4241_);
lean_dec(v___x_4240_);
v___x_4242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4243_ = lean_unsigned_to_nat(32u);
v___x_4244_ = lean_mk_empty_array_with_capacity(v___x_4243_);
lean_dec_ref(v___x_4244_);
v___x_4245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4246_, 0, v_env_4236_);
lean_ctor_set(v___x_4246_, 1, v___x_4242_);
lean_ctor_set(v___x_4246_, 2, v___x_4245_);
lean_ctor_set(v___x_4246_, 3, v_opts_4241_);
v___x_4247_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
lean_ctor_set(v___x_4247_, 1, v_msgData_4232_);
v___x_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4249_, v___y_4250_);
lean_dec(v___y_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Elab_Command_getRef___redArg(v___y_4254_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v_macroStack_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4272_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
v_macroStack_4259_ = lean_ctor_get(v___y_4254_, 4);
v___x_4260_ = l_Lean_Elab_getBetterRef(v_a_4258_, v_macroStack_4259_);
lean_dec(v_a_4258_);
v___x_4261_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msg_4253_, v___y_4255_);
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4261_);
lean_inc(v_macroStack_4259_);
v___x_4263_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_a_4262_, v_macroStack_4259_, v___y_4255_);
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4272_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4272_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4260_);
lean_ctor_set(v___x_4268_, 1, v_a_4264_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 1);
lean_ctor_set(v___x_4266_, 0, v___x_4268_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_msg_4253_);
v_a_4273_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4257_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4257_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_4286_, lean_object* v_msg_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Elab_Command_getRef___redArg(v___y_4288_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v_fileName_4293_; lean_object* v_fileMap_4294_; lean_object* v_currRecDepth_4295_; lean_object* v_cmdPos_4296_; lean_object* v_macroStack_4297_; lean_object* v_quotContext_x3f_4298_; lean_object* v_currMacroScope_4299_; lean_object* v_snap_x3f_4300_; lean_object* v_cancelTk_x3f_4301_; uint8_t v_suppressElabErrors_4302_; lean_object* v_ref_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v_fileName_4293_ = lean_ctor_get(v___y_4288_, 0);
v_fileMap_4294_ = lean_ctor_get(v___y_4288_, 1);
v_currRecDepth_4295_ = lean_ctor_get(v___y_4288_, 2);
v_cmdPos_4296_ = lean_ctor_get(v___y_4288_, 3);
v_macroStack_4297_ = lean_ctor_get(v___y_4288_, 4);
v_quotContext_x3f_4298_ = lean_ctor_get(v___y_4288_, 5);
v_currMacroScope_4299_ = lean_ctor_get(v___y_4288_, 6);
v_snap_x3f_4300_ = lean_ctor_get(v___y_4288_, 8);
v_cancelTk_x3f_4301_ = lean_ctor_get(v___y_4288_, 9);
v_suppressElabErrors_4302_ = lean_ctor_get_uint8(v___y_4288_, sizeof(void*)*10);
v_ref_4303_ = l_Lean_replaceRef(v_ref_4286_, v_a_4292_);
lean_dec(v_a_4292_);
lean_inc(v_cancelTk_x3f_4301_);
lean_inc(v_snap_x3f_4300_);
lean_inc(v_currMacroScope_4299_);
lean_inc(v_quotContext_x3f_4298_);
lean_inc(v_macroStack_4297_);
lean_inc(v_cmdPos_4296_);
lean_inc(v_currRecDepth_4295_);
lean_inc_ref(v_fileMap_4294_);
lean_inc_ref(v_fileName_4293_);
v___x_4304_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4304_, 0, v_fileName_4293_);
lean_ctor_set(v___x_4304_, 1, v_fileMap_4294_);
lean_ctor_set(v___x_4304_, 2, v_currRecDepth_4295_);
lean_ctor_set(v___x_4304_, 3, v_cmdPos_4296_);
lean_ctor_set(v___x_4304_, 4, v_macroStack_4297_);
lean_ctor_set(v___x_4304_, 5, v_quotContext_x3f_4298_);
lean_ctor_set(v___x_4304_, 6, v_currMacroScope_4299_);
lean_ctor_set(v___x_4304_, 7, v_ref_4303_);
lean_ctor_set(v___x_4304_, 8, v_snap_x3f_4300_);
lean_ctor_set(v___x_4304_, 9, v_cancelTk_x3f_4301_);
lean_ctor_set_uint8(v___x_4304_, sizeof(void*)*10, v_suppressElabErrors_4302_);
v___x_4305_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4287_, v___x_4304_, v___y_4289_);
lean_dec_ref_known(v___x_4304_, 10);
return v___x_4305_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_msg_4287_);
v_a_4306_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4291_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4291_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_4314_, lean_object* v_msg_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4314_, v_msg_4315_, v___y_4316_, v___y_4317_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v_ref_4314_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_4320_, lean_object* v_msg_4321_, lean_object* v_declHint_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; lean_object* v_a_4327_; lean_object* v___x_4328_; 
v___x_4326_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4321_, v_declHint_4322_, v___y_4323_, v___y_4324_);
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref(v___x_4326_);
v___x_4328_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4320_, v_a_4327_, v___y_4323_, v___y_4324_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_4329_, lean_object* v_msg_4330_, lean_object* v_declHint_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4329_, v_msg_4330_, v_declHint_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v_ref_4329_);
return v_res_4335_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0));
v___x_4338_ = l_Lean_stringToMessageData(v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_4339_, lean_object* v_constName_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; uint8_t v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4344_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4345_ = 0;
lean_inc(v_constName_4340_);
v___x_4346_ = l_Lean_MessageData_ofConstName(v_constName_4340_, v___x_4345_);
v___x_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4344_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4339_, v___x_4349_, v_constName_4340_, v___y_4341_, v___y_4342_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_4351_, lean_object* v_constName_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4351_, v_constName_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v_ref_4351_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_constName_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_Elab_Command_getRef___redArg(v___y_4358_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4363_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___x_4363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_a_4362_, v_constName_4357_, v___y_4358_, v___y_4359_);
lean_dec(v_a_4362_);
return v___x_4363_;
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec(v_constName_4357_);
v_a_4364_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4361_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4361_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_constName_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object* v_constName_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v_env_4382_; uint8_t v___x_4383_; lean_object* v___x_4384_; 
v___x_4381_ = lean_st_ref_get(v___y_4379_);
v_env_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref(v_env_4382_);
lean_dec(v___x_4381_);
v___x_4383_ = 0;
lean_inc(v_constName_4377_);
v___x_4384_ = l_Lean_Environment_find_x3f(v_env_4382_, v_constName_4377_, v___x_4383_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4377_, v___y_4378_, v___y_4379_);
return v___x_4385_;
}
else
{
lean_object* v_val_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v_constName_4377_);
v_val_4386_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4384_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_val_4386_);
lean_dec(v___x_4384_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 0);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_val_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object* v_constName_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_constName_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(uint8_t v___x_4399_, lean_object* v_x_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
if (lean_obj_tag(v_x_4400_) == 0)
{
uint8_t v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = 1;
v___x_4405_ = lean_box(v___x_4404_);
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
return v___x_4406_;
}
else
{
lean_object* v_head_4407_; lean_object* v_tail_4408_; lean_object* v___y_4410_; uint8_t v_a_4411_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_head_4407_ = lean_ctor_get(v_x_4400_, 0);
lean_inc(v_head_4407_);
v_tail_4408_ = lean_ctor_get(v_x_4400_, 1);
lean_inc(v_tail_4408_);
lean_dec_ref_known(v_x_4400_, 2);
v___x_4413_ = lean_unsigned_to_nat(0u);
v___x_4414_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_head_4407_, v___y_4401_, v___y_4402_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4430_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4430_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4430_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
if (lean_obj_tag(v_a_4415_) == 6)
{
lean_object* v_val_4419_; lean_object* v_numFields_4420_; uint8_t v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v_val_4419_ = lean_ctor_get(v_a_4415_, 0);
lean_inc_ref(v_val_4419_);
lean_dec_ref_known(v_a_4415_, 1);
v_numFields_4420_ = lean_ctor_get(v_val_4419_, 4);
lean_inc(v_numFields_4420_);
lean_dec_ref(v_val_4419_);
v___x_4421_ = lean_nat_dec_eq(v_numFields_4420_, v___x_4413_);
lean_dec(v_numFields_4420_);
v___x_4422_ = lean_box(v___x_4421_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4422_);
v___x_4424_ = v___x_4417_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
v___y_4410_ = v___x_4424_;
v_a_4411_ = v___x_4421_;
goto v___jp_4409_;
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
lean_dec(v_a_4415_);
v___x_4426_ = lean_box(v___x_4399_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4426_);
v___x_4428_ = v___x_4417_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
v___y_4410_ = v___x_4428_;
v_a_4411_ = v___x_4399_;
goto v___jp_4409_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_tail_4408_);
v_a_4431_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4414_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4414_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
v___jp_4409_:
{
if (v_a_4411_ == 0)
{
lean_dec(v_tail_4408_);
return v___y_4410_;
}
else
{
lean_dec_ref(v___y_4410_);
v_x_4400_ = v_tail_4408_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object* v___x_4439_, lean_object* v_x_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
uint8_t v___x_6811__boxed_4444_; lean_object* v_res_4445_; 
v___x_6811__boxed_4444_ = lean_unbox(v___x_4439_);
v_res_4445_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v___x_6811__boxed_4444_, v_x_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object* v_declName_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v___x_4450_; 
v___x_4450_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_declName_4446_, v___y_4447_, v___y_4448_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4506_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4506_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4506_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
if (lean_obj_tag(v_a_4451_) == 5)
{
lean_object* v_val_4455_; lean_object* v_toConstantVal_4456_; lean_object* v_numParams_4457_; lean_object* v_numIndices_4458_; lean_object* v_ctors_4459_; uint8_t v_isRec_4460_; uint8_t v_isUnsafe_4461_; lean_object* v_type_4462_; uint8_t v___x_4463_; 
v_val_4455_ = lean_ctor_get(v_a_4451_, 0);
lean_inc_ref(v_val_4455_);
lean_dec_ref_known(v_a_4451_, 1);
v_toConstantVal_4456_ = lean_ctor_get(v_val_4455_, 0);
v_numParams_4457_ = lean_ctor_get(v_val_4455_, 1);
lean_inc(v_numParams_4457_);
v_numIndices_4458_ = lean_ctor_get(v_val_4455_, 2);
lean_inc(v_numIndices_4458_);
v_ctors_4459_ = lean_ctor_get(v_val_4455_, 4);
lean_inc(v_ctors_4459_);
v_isRec_4460_ = lean_ctor_get_uint8(v_val_4455_, sizeof(void*)*6);
v_isUnsafe_4461_ = lean_ctor_get_uint8(v_val_4455_, sizeof(void*)*6 + 1);
v_type_4462_ = lean_ctor_get(v_toConstantVal_4456_, 2);
v___x_4463_ = l_Lean_Expr_isProp(v_type_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4464_ = l_Lean_InductiveVal_numTypeFormers(v_val_4455_);
lean_dec_ref(v_val_4455_);
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4466_ = lean_nat_dec_eq(v___x_4464_, v___x_4465_);
lean_dec(v___x_4464_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
lean_dec(v_ctors_4459_);
lean_dec(v_numIndices_4458_);
lean_dec(v_numParams_4457_);
v___x_4467_ = lean_box(v___x_4466_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4467_);
v___x_4469_ = v___x_4453_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
else
{
lean_object* v___x_4471_; uint8_t v___x_4472_; 
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = lean_nat_dec_eq(v_numIndices_4458_, v___x_4471_);
lean_dec(v_numIndices_4458_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
lean_dec(v_ctors_4459_);
lean_dec(v_numParams_4457_);
v___x_4473_ = lean_box(v___x_4472_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4473_);
v___x_4475_ = v___x_4453_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
else
{
uint8_t v___x_4477_; 
v___x_4477_ = lean_nat_dec_eq(v_numParams_4457_, v___x_4471_);
lean_dec(v_numParams_4457_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; lean_object* v___x_4480_; 
lean_dec(v_ctors_4459_);
v___x_4478_ = lean_box(v___x_4477_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4478_);
v___x_4480_ = v___x_4453_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
else
{
uint8_t v___x_4482_; 
v___x_4482_ = l_List_isEmpty___redArg(v_ctors_4459_);
if (v___x_4482_ == 0)
{
if (v_isRec_4460_ == 0)
{
if (v_isUnsafe_4461_ == 0)
{
lean_object* v___x_4483_; 
lean_del_object(v___x_4453_);
v___x_4483_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v_isUnsafe_4461_, v_ctors_4459_, v___y_4447_, v___y_4448_);
return v___x_4483_;
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
lean_dec(v_ctors_4459_);
v___x_4484_ = lean_box(v_isRec_4460_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4484_);
v___x_4486_ = v___x_4453_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4490_; 
lean_dec(v_ctors_4459_);
v___x_4488_ = lean_box(v___x_4482_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4488_);
v___x_4490_ = v___x_4453_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4488_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4494_; 
lean_dec(v_ctors_4459_);
v___x_4492_ = lean_box(v___x_4463_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4492_);
v___x_4494_ = v___x_4453_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
else
{
uint8_t v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
lean_dec(v_ctors_4459_);
lean_dec(v_numIndices_4458_);
lean_dec(v_numParams_4457_);
lean_dec_ref(v_val_4455_);
v___x_4496_ = 0;
v___x_4497_ = lean_box(v___x_4496_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4497_);
v___x_4499_ = v___x_4453_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4497_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
else
{
uint8_t v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_dec(v_a_4451_);
v___x_4501_ = 0;
v___x_4502_ = lean_box(v___x_4501_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4502_);
v___x_4504_ = v___x_4453_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
v_a_4507_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4450_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4450_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object* v_declName_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object* v_as_4520_, size_t v_i_4521_, size_t v_stop_4522_, lean_object* v_b_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v___x_4527_; 
v___x_4527_ = lean_usize_dec_eq(v_i_4521_, v_stop_4522_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = lean_array_uget_borrowed(v_as_4520_, v_i_4521_);
lean_inc(v___x_4528_);
v___x_4529_ = l_Lean_Elab_Command_elabCommand(v___x_4528_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; size_t v___x_4531_; size_t v___x_4532_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = ((size_t)1ULL);
v___x_4532_ = lean_usize_add(v_i_4521_, v___x_4531_);
v_i_4521_ = v___x_4532_;
v_b_4523_ = v_a_4530_;
goto _start;
}
else
{
return v___x_4529_;
}
}
else
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_b_4523_);
return v___x_4534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object* v_as_4535_, lean_object* v_i_4536_, lean_object* v_stop_4537_, lean_object* v_b_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
size_t v_i_boxed_4542_; size_t v_stop_boxed_4543_; lean_object* v_res_4544_; 
v_i_boxed_4542_ = lean_unbox_usize(v_i_4536_);
lean_dec(v_i_4536_);
v_stop_boxed_4543_ = lean_unbox_usize(v_stop_4537_);
lean_dec(v_stop_4537_);
v_res_4544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_as_4535_, v_i_boxed_4542_, v_stop_boxed_4543_, v_b_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_as_4535_);
return v_res_4544_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10));
v___x_4573_ = l_String_toRawSubstring_x27(v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object* v___x_4577_, lean_object* v_declName_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v_a_4586_; lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4577_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4685_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4685_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4685_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___y_4652_; lean_object* v___x_4653_; 
lean_inc(v_declName_4578_);
v___x_4653_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___y_4655_; lean_object* v___x_4656_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4653_, 1);
lean_inc(v_a_4614_);
v___y_4655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed), 10, 3);
lean_closure_set(v___y_4655_, 0, v_a_4654_);
lean_closure_set(v___y_4655_, 1, v_a_4614_);
lean_closure_set(v___y_4655_, 2, v_declName_4578_);
v___x_4656_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_4655_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref_known(v___x_4656_, 1);
v___x_4658_ = lean_unsigned_to_nat(0u);
v___x_4659_ = lean_array_get_size(v_a_4657_);
v___x_4660_ = lean_nat_dec_lt(v___x_4658_, v___x_4659_);
if (v___x_4660_ == 0)
{
lean_dec(v_a_4657_);
goto v___jp_4618_;
}
else
{
lean_object* v___x_4661_; uint8_t v___x_4662_; 
v___x_4661_ = lean_box(0);
v___x_4662_ = lean_nat_dec_le(v___x_4659_, v___x_4659_);
if (v___x_4662_ == 0)
{
if (v___x_4660_ == 0)
{
lean_dec(v_a_4657_);
goto v___jp_4618_;
}
else
{
size_t v___x_4663_; size_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = ((size_t)0ULL);
v___x_4664_ = lean_usize_of_nat(v___x_4659_);
v___x_4665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4657_, v___x_4663_, v___x_4664_, v___x_4661_, v___y_4579_, v___y_4580_);
lean_dec(v_a_4657_);
v___y_4652_ = v___x_4665_;
goto v___jp_4651_;
}
}
else
{
size_t v___x_4666_; size_t v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((size_t)0ULL);
v___x_4667_ = lean_usize_of_nat(v___x_4659_);
v___x_4668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4657_, v___x_4666_, v___x_4667_, v___x_4661_, v___y_4579_, v___y_4580_);
lean_dec(v_a_4657_);
v___y_4652_ = v___x_4668_;
goto v___jp_4651_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
lean_del_object(v___x_4616_);
lean_dec(v_a_4614_);
lean_dec_ref(v___y_4579_);
v_a_4669_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4656_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4656_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_del_object(v___x_4616_);
lean_dec(v_a_4614_);
lean_dec_ref(v___y_4579_);
lean_dec(v_declName_4578_);
v_a_4677_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4653_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4653_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
v___jp_4618_:
{
uint8_t v_usePartial_4619_; 
v_usePartial_4619_ = lean_ctor_get_uint8(v_a_4614_, sizeof(void*)*3);
if (v_usePartial_4619_ == 0)
{
lean_object* v_instName_4620_; lean_object* v___x_4621_; 
lean_del_object(v___x_4616_);
v_instName_4620_ = lean_ctor_get(v_a_4614_, 0);
lean_inc(v_instName_4620_);
lean_dec(v_a_4614_);
v___x_4621_ = l_Lean_Elab_Command_getRef___redArg(v___y_4579_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v___x_4621_, 1);
v___x_4623_ = l_Lean_SourceInfo_fromRef(v_a_4622_, v_usePartial_4619_);
lean_dec(v_a_4622_);
v___x_4624_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4579_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_quotContext_x3f_4625_; 
v_quotContext_x3f_4625_ = lean_ctor_get(v___y_4579_, 5);
if (lean_obj_tag(v_quotContext_x3f_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4627_; lean_object* v_a_4628_; 
v_a_4626_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4626_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4627_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4580_);
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref(v___x_4627_);
v___y_4583_ = v_a_4626_;
v___y_4584_ = v_instName_4620_;
v___y_4585_ = v___x_4623_;
v_a_4586_ = v_a_4628_;
goto v___jp_4582_;
}
else
{
lean_object* v_a_4629_; lean_object* v_val_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4624_, 1);
v_val_4630_ = lean_ctor_get(v_quotContext_x3f_4625_, 0);
lean_inc(v_val_4630_);
v___y_4583_ = v_a_4629_;
v___y_4584_ = v_instName_4620_;
v___y_4585_ = v___x_4623_;
v_a_4586_ = v_val_4630_;
goto v___jp_4582_;
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec(v___x_4623_);
lean_dec(v_instName_4620_);
lean_dec_ref(v___y_4579_);
v_a_4631_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4624_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4624_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec(v_instName_4620_);
lean_dec_ref(v___y_4579_);
v_a_4639_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4621_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4621_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4649_; 
lean_dec(v_a_4614_);
lean_dec_ref(v___y_4579_);
v___x_4647_ = lean_box(0);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4647_);
v___x_4649_ = v___x_4616_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
v___jp_4651_:
{
if (lean_obj_tag(v___y_4652_) == 0)
{
lean_dec_ref_known(v___y_4652_, 1);
goto v___jp_4618_;
}
else
{
lean_del_object(v___x_4616_);
lean_dec(v_a_4614_);
lean_dec_ref(v___y_4579_);
return v___y_4652_;
}
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec_ref(v___y_4579_);
lean_dec(v_declName_4578_);
v_a_4686_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4613_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4613_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
v___jp_4582_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4587_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0));
v___x_4588_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1));
lean_inc_n(v___y_4585_, 10);
v___x_4589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___y_4585_);
lean_ctor_set(v___x_4589_, 1, v___x_4587_);
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2));
v___x_4591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___y_4585_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
v___x_4592_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_4593_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4));
v___x_4594_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6));
v___x_4595_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_4596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4596_, 0, v___y_4585_);
lean_ctor_set(v___x_4596_, 1, v___x_4592_);
lean_ctor_set(v___x_4596_, 2, v___x_4595_);
lean_inc_ref(v___x_4596_);
v___x_4597_ = l_Lean_Syntax_node1(v___y_4585_, v___x_4594_, v___x_4596_);
v___x_4598_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9));
v___x_4599_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11);
v___x_4600_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12));
v___x_4601_ = l_Lean_addMacroScope(v_a_4586_, v___x_4600_, v___y_4583_);
v___x_4602_ = lean_box(0);
v___x_4603_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4603_, 0, v___y_4585_);
lean_ctor_set(v___x_4603_, 1, v___x_4599_);
lean_ctor_set(v___x_4603_, 2, v___x_4601_);
lean_ctor_set(v___x_4603_, 3, v___x_4602_);
v___x_4604_ = l_Lean_Syntax_node2(v___y_4585_, v___x_4598_, v___x_4603_, v___x_4596_);
v___x_4605_ = l_Lean_Syntax_node2(v___y_4585_, v___x_4593_, v___x_4597_, v___x_4604_);
v___x_4606_ = l_Lean_Syntax_node1(v___y_4585_, v___x_4592_, v___x_4605_);
v___x_4607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13));
v___x_4608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___y_4585_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = l_Lean_mkIdent(v___y_4584_);
v___x_4610_ = l_Lean_Syntax_node1(v___y_4585_, v___x_4592_, v___x_4609_);
v___x_4611_ = l_Lean_Syntax_node5(v___y_4585_, v___x_4588_, v___x_4589_, v___x_4591_, v___x_4606_, v___x_4608_, v___x_4610_);
v___x_4612_ = l_Lean_Elab_Command_elabCommand(v___x_4611_, v___y_4579_, v___y_4580_);
lean_dec_ref(v___y_4579_);
return v___x_4612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object* v___x_4694_, lean_object* v_declName_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(v___x_4694_, v_declName_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object* v_declName_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___f_4709_; lean_object* v___x_4710_; 
v___x_4704_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_4705_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_4706_ = 1;
v___x_4707_ = lean_box(v___x_4706_);
lean_inc_n(v_declName_4700_, 2);
v___x_4708_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkContext___boxed), 11, 4);
lean_closure_set(v___x_4708_, 0, v___x_4704_);
lean_closure_set(v___x_4708_, 1, v___x_4705_);
lean_closure_set(v___x_4708_, 2, v_declName_4700_);
lean_closure_set(v___x_4708_, 3, v___x_4707_);
v___f_4709_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed), 5, 2);
lean_closure_set(v___f_4709_, 0, v___x_4708_);
lean_closure_set(v___f_4709_, 1, v_declName_4700_);
v___x_4710_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4700_, v___f_4709_, v_a_4701_, v_a_4702_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object* v_declName_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_declName_4711_, v_a_4712_, v_a_4713_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_4716_, lean_object* v_constName_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4717_, v___y_4718_, v___y_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4722_, lean_object* v_constName_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(v_00_u03b1_4722_, v_constName_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4728_, lean_object* v_ref_4729_, lean_object* v_constName_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4729_, v_constName_4730_, v___y_4731_, v___y_4732_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4735_, lean_object* v_ref_4736_, lean_object* v_constName_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_4735_, v_ref_4736_, v_constName_4737_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec(v_ref_4736_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4742_, lean_object* v_ref_4743_, lean_object* v_msg_4744_, lean_object* v_declHint_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4743_, v_msg_4744_, v_declHint_4745_, v___y_4746_, v___y_4747_);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4750_, lean_object* v_ref_4751_, lean_object* v_msg_4752_, lean_object* v_declHint_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4750_, v_ref_4751_, v_msg_4752_, v_declHint_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v_ref_4751_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_4758_, lean_object* v_declHint_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4758_, v_declHint_4759_, v___y_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_4764_, lean_object* v_declHint_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_4764_, v_declHint_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_4770_, lean_object* v_ref_4771_, lean_object* v_msg_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4771_, v_msg_4772_, v___y_4773_, v___y_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_ref_4778_, lean_object* v_msg_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_4777_, v_ref_4778_, v_msg_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v_ref_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4784_, v___y_4786_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_4789_, v___y_4790_, v___y_4791_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
return v_res_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_4794_, lean_object* v_msg_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4795_, v___y_4796_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4800_, lean_object* v_msg_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4800_, v_msg_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object* v_msgData_4806_, lean_object* v_macroStack_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4806_, v_macroStack_4807_, v___y_4809_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object* v_msgData_4812_, lean_object* v_macroStack_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(v_msgData_4812_, v_macroStack_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v_env_4822_; uint8_t v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4821_ = lean_st_ref_get(v___y_4819_);
v_env_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc_ref(v_env_4822_);
lean_dec(v___x_4821_);
v___x_4823_ = l_Lean_isInductiveCore(v_env_4822_, v_declName_4818_);
v___x_4824_ = lean_box(v___x_4823_);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4826_, v___y_4827_);
lean_dec(v___y_4827_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object* v_declName_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4830_, v___y_4832_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(v_declName_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t v_____do__lift_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
if (v_____do__lift_4840_ == 0)
{
uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4844_ = 1;
v___x_4845_ = lean_box(v___x_4844_);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
return v___x_4846_;
}
else
{
uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4847_ = 0;
v___x_4848_ = lean_box(v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
uint8_t v_____do__lift_1654__boxed_4854_; lean_object* v_res_4855_; 
v_____do__lift_1654__boxed_4854_ = lean_unbox(v_____do__lift_4850_);
v_res_4855_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v_____do__lift_1654__boxed_4854_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object* v_as_4856_, size_t v_i_4857_, size_t v_stop_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v___x_4866_; 
v___x_4866_ = lean_usize_dec_eq(v_i_4857_, v_stop_4858_);
if (v___x_4866_ == 0)
{
uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4867_ = 1;
v___x_4868_ = lean_array_uget_borrowed(v_as_4856_, v_i_4857_);
lean_inc(v___x_4868_);
v___x_4869_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v___x_4868_, v___y_4860_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4879_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4879_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4879_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
uint8_t v___x_4874_; 
v___x_4874_ = lean_unbox(v_a_4870_);
lean_dec(v_a_4870_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4875_ = lean_box(v___x_4867_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v___x_4875_);
v___x_4877_ = v___x_4872_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
else
{
lean_del_object(v___x_4872_);
goto v___jp_4862_;
}
}
}
else
{
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4889_; 
v_a_4880_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4882_ = v___x_4869_;
v_isShared_4883_ = v_isSharedCheck_4889_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4869_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4889_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_unbox(v_a_4880_);
lean_dec(v_a_4880_);
if (v___x_4884_ == 0)
{
lean_del_object(v___x_4882_);
goto v___jp_4862_;
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_box(v___x_4867_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set_tag(v___x_4882_, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4885_);
v___x_4887_ = v___x_4882_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
return v___x_4869_;
}
}
}
else
{
uint8_t v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4890_ = 0;
v___x_4891_ = lean_box(v___x_4890_);
v___x_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4891_);
return v___x_4892_;
}
v___jp_4862_:
{
size_t v___x_4863_; size_t v___x_4864_; 
v___x_4863_ = ((size_t)1ULL);
v___x_4864_ = lean_usize_add(v_i_4857_, v___x_4863_);
v_i_4857_ = v___x_4864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object* v_as_4893_, lean_object* v_i_4894_, lean_object* v_stop_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
size_t v_i_boxed_4899_; size_t v_stop_boxed_4900_; lean_object* v_res_4901_; 
v_i_boxed_4899_ = lean_unbox_usize(v_i_4894_);
lean_dec(v_i_4894_);
v_stop_boxed_4900_ = lean_unbox_usize(v_stop_4895_);
lean_dec(v_stop_4895_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_as_4893_, v_i_boxed_4899_, v_stop_boxed_4900_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec_ref(v_as_4893_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object* v_as_4902_, size_t v_sz_4903_, size_t v_i_4904_, lean_object* v_b_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
uint8_t v___x_4909_; 
v___x_4909_ = lean_usize_dec_lt(v_i_4904_, v_sz_4903_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; 
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_b_4905_);
return v___x_4910_;
}
else
{
lean_object* v___x_4911_; lean_object* v_a_4912_; lean_object* v___x_4913_; 
v___x_4911_ = lean_box(0);
v_a_4912_ = lean_array_uget_borrowed(v_as_4902_, v_i_4904_);
lean_inc(v_a_4912_);
v___x_4913_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_a_4912_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4913_) == 0)
{
size_t v___x_4914_; size_t v___x_4915_; 
lean_dec_ref_known(v___x_4913_, 1);
v___x_4914_ = ((size_t)1ULL);
v___x_4915_ = lean_usize_add(v_i_4904_, v___x_4914_);
v_i_4904_ = v___x_4915_;
v_b_4905_ = v___x_4911_;
goto _start;
}
else
{
return v___x_4913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object* v_as_4917_, lean_object* v_sz_4918_, lean_object* v_i_4919_, lean_object* v_b_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
size_t v_sz_boxed_4924_; size_t v_i_boxed_4925_; lean_object* v_res_4926_; 
v_sz_boxed_4924_ = lean_unbox_usize(v_sz_4918_);
lean_dec(v_sz_4918_);
v_i_boxed_4925_ = lean_unbox_usize(v_i_4919_);
lean_dec(v_i_4919_);
v_res_4926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_as_4917_, v_sz_boxed_4924_, v_i_boxed_4925_, v_b_4920_, v___y_4921_, v___y_4922_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec_ref(v_as_4917_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object* v_declNames_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v___y_4955_; lean_object* v___x_4958_; lean_object* v___x_4959_; uint8_t v___x_4960_; 
v___x_4958_ = lean_unsigned_to_nat(0u);
v___x_4959_ = lean_array_get_size(v_declNames_4927_);
v___x_4960_ = lean_nat_dec_lt(v___x_4958_, v___x_4959_);
if (v___x_4960_ == 0)
{
lean_object* v___x_4961_; 
v___x_4961_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4960_, v_a_4928_, v_a_4929_);
v___y_4955_ = v___x_4961_;
goto v___jp_4954_;
}
else
{
if (v___x_4960_ == 0)
{
goto v___jp_4931_;
}
else
{
size_t v___x_4962_; size_t v___x_4963_; lean_object* v___x_4964_; 
v___x_4962_ = ((size_t)0ULL);
v___x_4963_ = lean_usize_of_nat(v___x_4959_);
v___x_4964_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_declNames_4927_, v___x_4962_, v___x_4963_, v_a_4928_, v_a_4929_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
v___x_4966_ = lean_unbox(v_a_4965_);
lean_dec(v_a_4965_);
v___x_4967_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4966_, v_a_4928_, v_a_4929_);
v___y_4955_ = v___x_4967_;
goto v___jp_4954_;
}
else
{
v___y_4955_ = v___x_4964_;
goto v___jp_4954_;
}
}
}
v___jp_4931_:
{
uint8_t v___x_4932_; lean_object* v___x_4933_; size_t v_sz_4934_; size_t v___x_4935_; lean_object* v___x_4936_; 
v___x_4932_ = 1;
v___x_4933_ = lean_box(0);
v_sz_4934_ = lean_array_size(v_declNames_4927_);
v___x_4935_ = ((size_t)0ULL);
v___x_4936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_declNames_4927_, v_sz_4934_, v___x_4935_, v___x_4933_, v_a_4928_, v_a_4929_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4944_; 
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4944_ == 0)
{
lean_object* v_unused_4945_; 
v_unused_4945_ = lean_ctor_get(v___x_4936_, 0);
lean_dec(v_unused_4945_);
v___x_4938_ = v___x_4936_;
v_isShared_4939_ = v_isSharedCheck_4944_;
goto v_resetjp_4937_;
}
else
{
lean_dec(v___x_4936_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4944_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4940_ = lean_box(v___x_4932_);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v___x_4940_);
v___x_4942_ = v___x_4938_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
v_a_4946_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4936_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4936_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
v___jp_4954_:
{
if (lean_obj_tag(v___y_4955_) == 0)
{
lean_object* v_a_4956_; uint8_t v___x_4957_; 
v_a_4956_ = lean_ctor_get(v___y_4955_, 0);
v___x_4957_ = lean_unbox(v_a_4956_);
if (v___x_4957_ == 0)
{
return v___y_4955_;
}
else
{
lean_dec_ref_known(v___y_4955_, 1);
goto v___jp_4931_;
}
}
else
{
return v___y_4955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object* v_declNames_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(v_declNames_4968_, v_a_4969_, v_a_4970_);
lean_dec(v_a_4970_);
lean_dec_ref(v_a_4969_);
lean_dec_ref(v_declNames_4968_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_5010_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5011_ = l_Lean_Elab_registerDerivingHandler(v___x_5009_, v___x_5010_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
lean_dec_ref_known(v___x_5011_, 1);
v___x_5012_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_5013_ = 0;
v___x_5014_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5015_ = l_Lean_registerTraceClass(v___x_5012_, v___x_5013_, v___x_5014_);
return v___x_5015_;
}
else
{
return v___x_5011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
return v_res_5017_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold);
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_BEq(builtin);
}
#ifdef __cplusplus
}
#endif
