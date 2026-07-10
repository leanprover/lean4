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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v_ref_125_ = lean_ctor_get(v___y_122_, 5);
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
v_ref_153_ = lean_ctor_get(v___y_149_, 5);
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
v___x_214_ = l_Array_mkArray0(lean_box(0));
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
lean_object* v_a_231_; lean_object* v_ref_232_; lean_object* v_quotContext_233_; lean_object* v_currMacroScope_234_; lean_object* v___x_235_; lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_274_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_ref_232_ = lean_ctor_get(v_a_224_, 5);
v_quotContext_233_ = lean_ctor_get(v_a_224_, 10);
v_currMacroScope_234_ = lean_ctor_get(v_a_224_, 11);
v___x_235_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_274_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_274_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_274_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_242_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_243_ = 0;
v___x_244_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_243_);
v___x_245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_244_);
v___x_246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_248_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_249_ = l_Lean_Syntax_node1(v___x_244_, v___x_248_, v___x_246_);
lean_inc(v___x_249_);
v___x_250_ = lean_array_push(v_a_231_, v___x_249_);
v___x_251_ = lean_array_push(v___x_250_, v___x_249_);
lean_inc(v_currMacroScope_234_);
lean_inc(v_quotContext_233_);
v___x_252_ = l_Lean_addMacroScope(v_quotContext_233_, v___x_247_, v_currMacroScope_234_);
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_254_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_254_, 0, v_a_236_);
lean_ctor_set(v___x_254_, 1, v___x_242_);
lean_ctor_set(v___x_254_, 2, v___x_252_);
lean_ctor_set(v___x_254_, 3, v___x_253_);
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc_n(v_a_238_, 4);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v_a_238_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_259_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v_sz_260_ = lean_array_size(v___x_251_);
v___x_261_ = ((size_t)0ULL);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_260_, v___x_261_, v___x_251_);
v___x_263_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_264_ = l_Lean_mkSepArray(v___x_262_, v___x_263_);
lean_dec_ref(v___x_262_);
v___x_265_ = l_Array_append___redArg(v___x_259_, v___x_264_);
lean_dec_ref(v___x_264_);
v___x_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_266_, 0, v_a_238_);
lean_ctor_set(v___x_266_, 1, v___x_258_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
v___x_267_ = l_Lean_Syntax_node1(v_a_238_, v___x_258_, v___x_266_);
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_269_, 0, v_a_238_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_Syntax_node4(v_a_238_, v___x_255_, v___x_257_, v___x_267_, v___x_269_, v___x_254_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_270_);
v___x_272_ = v___x_240_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_230_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_230_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object* v_indVal_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_indVal_283_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object* v_upperBound_292_, lean_object* v_inst_293_, lean_object* v_R_294_, lean_object* v_a_295_, lean_object* v_b_296_, lean_object* v_c_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_292_, v_a_295_, v_b_296_, v___y_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object* v_upperBound_306_, lean_object* v_inst_307_, lean_object* v_R_308_, lean_object* v_a_309_, lean_object* v_b_310_, lean_object* v_c_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(v_upperBound_306_, v_inst_307_, v_R_308_, v_a_309_, v_b_310_, v_c_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v_upperBound_306_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v_b_323_, lean_object* v_c_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_322_);
lean_inc_ref(v___y_321_);
v___x_330_ = lean_apply_9(v_k_320_, v_b_323_, v_c_324_, v___y_321_, v___y_322_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v_b_334_, lean_object* v_c_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(v_k_331_, v___y_332_, v___y_333_, v_b_334_, v_c_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_type_342_, lean_object* v_k_343_, uint8_t v_cleanupAnnotations_344_, uint8_t v_whnfType_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; 
lean_inc(v___y_347_);
lean_inc_ref(v___y_346_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_353_, 0, v_k_343_);
lean_closure_set(v___f_353_, 1, v___y_346_);
lean_closure_set(v___f_353_, 2, v___y_347_);
v___x_354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_342_, v___f_353_, v_cleanupAnnotations_344_, v_whnfType_345_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_354_) == 0)
{
return v___x_354_;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_type_363_, lean_object* v_k_364_, lean_object* v_cleanupAnnotations_365_, lean_object* v_whnfType_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_374_; uint8_t v_whnfType_boxed_375_; lean_object* v_res_376_; 
v_cleanupAnnotations_boxed_374_ = lean_unbox(v_cleanupAnnotations_365_);
v_whnfType_boxed_375_ = lean_unbox(v_whnfType_366_);
v_res_376_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_363_, v_k_364_, v_cleanupAnnotations_boxed_374_, v_whnfType_boxed_375_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object* v_00_u03b1_377_, lean_object* v_type_378_, lean_object* v_k_379_, uint8_t v_cleanupAnnotations_380_, uint8_t v_whnfType_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_378_, v_k_379_, v_cleanupAnnotations_380_, v_whnfType_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_390_, lean_object* v_type_391_, lean_object* v_k_392_, lean_object* v_cleanupAnnotations_393_, lean_object* v_whnfType_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_402_; uint8_t v_whnfType_boxed_403_; lean_object* v_res_404_; 
v_cleanupAnnotations_boxed_402_ = lean_unbox(v_cleanupAnnotations_393_);
v_whnfType_boxed_403_ = lean_unbox(v_whnfType_394_);
v_res_404_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(v_00_u03b1_390_, v_type_391_, v_k_392_, v_cleanupAnnotations_boxed_402_, v_whnfType_boxed_403_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v___x_405_, lean_object* v_as_406_, size_t v_i_407_, size_t v_stop_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_eq(v_i_407_, v_stop_408_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_array_uget_borrowed(v_as_406_, v_i_407_);
lean_inc(v___y_412_);
lean_inc_ref(v___y_411_);
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___x_415_);
v___x_416_ = lean_infer_type(v___x_415_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_430_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = l_Lean_Expr_fvarId_x21(v___x_405_);
v___x_422_ = l_Lean_Expr_containsFVar(v_a_417_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v_a_417_);
if (v___x_422_ == 0)
{
size_t v___x_423_; size_t v___x_424_; 
lean_del_object(v___x_419_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_i_407_, v___x_423_);
v_i_407_ = v___x_424_;
goto _start;
}
else
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_box(v___x_422_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_426_);
v___x_428_ = v___x_419_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_416_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_416_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = 0;
v___x_440_ = lean_box(v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v___x_442_, lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_stop_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
size_t v_i_boxed_451_; size_t v_stop_boxed_452_; lean_object* v_res_453_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_stop_boxed_452_ = lean_unbox_usize(v_stop_445_);
lean_dec(v_stop_445_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_442_, v_as_443_, v_i_boxed_451_, v_stop_boxed_452_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_as_443_);
lean_dec_ref(v___x_442_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_ref_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_ref_461_ = lean_ctor_get(v___y_458_, 5);
v___x_462_ = 0;
v___x_463_ = l_Lean_SourceInfo_fromRef(v_ref_461_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_472_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15));
v___x_497_ = l_String_toRawSubstring_x27(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_552_ = l_String_toRawSubstring_x27(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53));
v___x_589_ = l_String_toRawSubstring_x27(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_623_, lean_object* v_indVal_624_, lean_object* v___x_625_, lean_object* v_xs_626_, lean_object* v_a_627_, lean_object* v_auxFunName_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_a_639_; uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_lt(v_a_629_, v_upperBound_623_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v_b_630_);
return v___x_644_;
}
else
{
lean_object* v_snd_645_; lean_object* v_snd_646_; lean_object* v_fst_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_999_; 
v_snd_645_ = lean_ctor_get(v_b_630_, 1);
lean_inc(v_snd_645_);
v_snd_646_ = lean_ctor_get(v_snd_645_, 1);
lean_inc(v_snd_646_);
v_fst_647_ = lean_ctor_get(v_b_630_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_b_630_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_b_630_, 1);
lean_dec(v_unused_1000_);
v___x_649_ = v_b_630_;
v_isShared_650_ = v_isSharedCheck_999_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_fst_647_);
lean_dec(v_b_630_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_999_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_997_; 
v_fst_651_ = lean_ctor_get(v_snd_645_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_snd_645_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_snd_645_, 1);
lean_dec(v_unused_998_);
v___x_653_ = v_snd_645_;
v_isShared_654_ = v_isSharedCheck_997_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_fst_651_);
lean_dec(v_snd_645_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_997_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_996_; 
v_fst_655_ = lean_ctor_get(v_snd_646_, 0);
v_snd_656_ = lean_ctor_get(v_snd_646_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_snd_646_);
if (v_isSharedCheck_996_ == 0)
{
v___x_658_ = v_snd_646_;
v_isShared_659_ = v_isSharedCheck_996_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec(v_snd_646_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_996_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_toConstantVal_660_; lean_object* v_numParams_661_; lean_object* v_lctx_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_toConstantVal_660_ = lean_ctor_get(v_indVal_624_, 0);
lean_inc_ref(v_toConstantVal_660_);
v_numParams_661_ = lean_ctor_get(v_indVal_624_, 1);
v_lctx_662_ = lean_ctor_get(v___y_633_, 2);
v___x_663_ = l_Lean_instInhabitedExpr;
v___x_664_ = lean_nat_add(v_numParams_661_, v___x_625_);
v___x_665_ = lean_nat_sub(v___x_664_, v_a_629_);
lean_dec(v___x_664_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_sub(v___x_665_, v___x_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_array_get_borrowed(v___x_663_, v_xs_626_, v___x_667_);
lean_inc(v___x_668_);
lean_inc_ref(v_lctx_662_);
v___x_669_ = l_Lean_Meta_occursOrInType(v_lctx_662_, v___x_668_, v_a_627_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_671_ = l_Lean_Core_mkFreshUserName(v___x_670_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3));
v___x_674_ = l_Lean_Core_mkFreshUserName(v___x_673_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___x_668_);
v___x_676_ = lean_infer_type(v___x_668_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_n(v_a_677_, 2);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Meta_isProp(v_a_677_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = l_Lean_mkIdent(v_a_672_);
v___x_681_ = l_Lean_mkIdent(v_a_675_);
lean_inc(v___x_680_);
v___x_682_ = lean_array_push(v_fst_647_, v___x_680_);
lean_inc(v___x_681_);
v___x_683_ = lean_array_push(v_fst_651_, v___x_681_);
v___x_684_ = lean_unbox(v_a_679_);
if (v___x_684_ == 0)
{
lean_object* v_name_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_913_; 
v_name_685_ = lean_ctor_get(v_toConstantVal_660_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_toConstantVal_660_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_914_ = lean_ctor_get(v_toConstantVal_660_, 2);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_toConstantVal_660_, 1);
lean_dec(v_unused_915_);
v___x_687_ = v_toConstantVal_660_;
v_isShared_688_ = v_isSharedCheck_913_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_name_685_);
lean_dec(v_toConstantVal_660_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_913_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint8_t v___x_689_; uint8_t v_a_691_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v_lower_859_; lean_object* v_upper_860_; 
v___x_689_ = l_Lean_Expr_isAppOf(v_a_677_, v_name_685_);
lean_dec(v_name_685_);
lean_dec(v_a_677_);
if (v___x_689_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
lean_dec(v_a_679_);
v___x_868_ = lean_nat_add(v___x_667_, v___x_666_);
lean_dec(v___x_667_);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_array_get_size(v_xs_626_);
v___x_871_ = lean_nat_dec_le(v___x_868_, v___x_869_);
if (v___x_871_ == 0)
{
v_lower_859_ = v___x_868_;
v_upper_860_ = v___x_870_;
goto v___jp_858_;
}
else
{
lean_dec(v___x_868_);
v_lower_859_ = v___x_869_;
v_upper_860_ = v___x_870_;
goto v___jp_858_;
}
}
else
{
uint8_t v___x_872_; 
lean_del_object(v___x_687_);
lean_dec(v___x_667_);
lean_del_object(v___x_658_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
v___x_872_ = lean_unbox(v_snd_656_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec(v_a_679_);
v___x_873_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_n(v_a_874_, 4);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_876_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_628_);
v___x_877_ = l_Lean_mkIdent(v_auxFunName_628_);
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_879_ = l_Lean_Syntax_node2(v_a_874_, v___x_878_, v___x_680_, v___x_681_);
v___x_880_ = l_Lean_Syntax_node2(v_a_874_, v___x_876_, v___x_877_, v___x_879_);
v___x_881_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_882_, 0, v_a_874_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_Syntax_node3(v_a_874_, v___x_875_, v___x_880_, v___x_882_, v_fst_655_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_snd_656_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_683_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_682_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v_a_639_ = v___x_886_;
goto v___jp_638_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_887_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_873_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_873_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
v___x_895_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_n(v_a_896_, 2);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_628_);
v___x_898_ = l_Lean_mkIdent(v_auxFunName_628_);
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_900_ = l_Lean_Syntax_node2(v_a_896_, v___x_899_, v___x_680_, v___x_681_);
v___x_901_ = l_Lean_Syntax_node2(v_a_896_, v___x_897_, v___x_898_, v___x_900_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_a_679_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_683_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_682_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v_a_639_ = v___x_904_;
goto v___jp_638_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_dec(v_a_679_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_905_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_895_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_895_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
v___jp_690_:
{
if (v_a_691_ == 0)
{
uint8_t v___x_692_; 
lean_del_object(v___x_687_);
v___x_692_ = lean_unbox(v_snd_656_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_n(v_a_694_, 4);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v_a_694_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_Lean_Syntax_node3(v_a_694_, v___x_696_, v___x_680_, v___x_698_, v___x_681_);
v___x_700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_701_, 0, v_a_694_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_Syntax_node3(v_a_694_, v___x_695_, v___x_699_, v___x_701_, v_fst_655_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_702_);
v___x_704_ = v___x_658_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_snd_656_);
v___x_704_ = v_reuseFailAlloc_711_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_704_);
lean_ctor_set(v___x_653_, 0, v___x_683_);
v___x_706_ = v___x_653_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_706_);
lean_ctor_set(v___x_649_, 0, v___x_682_);
v___x_708_ = v___x_649_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_a_639_ = v___x_708_;
goto v___jp_638_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_712_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_693_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_693_);
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
}
else
{
lean_object* v___x_720_; 
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
v___x_720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_n(v_a_721_, 2);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_723_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v_a_721_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_Syntax_node3(v_a_721_, v___x_722_, v___x_680_, v___x_724_, v___x_681_);
v___x_726_ = lean_box(v_a_691_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_726_);
lean_ctor_set(v___x_658_, 0, v___x_725_);
v___x_728_ = v___x_658_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_735_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_728_);
lean_ctor_set(v___x_653_, 0, v___x_683_);
v___x_730_ = v___x_653_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_730_);
lean_ctor_set(v___x_649_, 0, v___x_682_);
v___x_732_ = v___x_649_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v_a_639_ = v___x_732_;
goto v___jp_638_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_del_object(v___x_658_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_736_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_720_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_720_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
lean_object* v___x_744_; 
lean_dec(v_snd_656_);
v___x_744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_quotContext_746_; lean_object* v_currMacroScope_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_n(v_a_745_, 11);
lean_dec_ref_known(v___x_744_, 1);
v_quotContext_746_ = lean_ctor_get(v___y_635_, 10);
v_currMacroScope_747_ = lean_ctor_get(v___y_635_, 11);
v___x_748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v_a_745_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_752_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_753_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc(v_currMacroScope_747_);
lean_inc(v_quotContext_746_);
v___x_754_ = l_Lean_addMacroScope(v_quotContext_746_, v___x_753_, v_currMacroScope_747_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_756_, 0, v_a_745_);
lean_ctor_set(v___x_756_, 1, v___x_752_);
lean_ctor_set(v___x_756_, 2, v___x_754_);
lean_ctor_set(v___x_756_, 3, v___x_755_);
lean_inc_ref(v___x_756_);
v___x_757_ = l_Lean_Syntax_node1(v_a_745_, v___x_751_, v___x_756_);
v___x_758_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_745_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_745_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Syntax_node3(v_a_745_, v___x_760_, v___x_680_, v___x_762_, v___x_681_);
v___x_764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v_a_745_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_745_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_772_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v_a_745_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
v___x_775_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 1);
lean_ctor_set(v___x_687_, 2, v___x_776_);
lean_ctor_set(v___x_687_, 1, v___x_771_);
lean_ctor_set(v___x_687_, 0, v_a_745_);
v___x_778_ = v___x_687_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_745_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_776_);
v___x_778_ = v_reuseFailAlloc_831_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v_a_745_, 20);
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_745_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_784_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_785_ = lean_box(0);
lean_inc_n(v_currMacroScope_747_, 3);
lean_inc_n(v_quotContext_746_, 3);
v___x_786_ = l_Lean_addMacroScope(v_quotContext_746_, v___x_785_, v_currMacroScope_747_);
v___x_787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_788_, 0, v_a_745_);
lean_ctor_set(v___x_788_, 1, v___x_784_);
lean_ctor_set(v___x_788_, 2, v___x_786_);
lean_ctor_set(v___x_788_, 3, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v_a_745_, v___x_783_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v_a_745_, v___x_780_, v___x_782_, v___x_789_);
v___x_791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_792_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_794_ = l_Lean_addMacroScope(v_quotContext_746_, v___x_793_, v_currMacroScope_747_);
v___x_795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_796_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_796_, 0, v_a_745_);
lean_ctor_set(v___x_796_, 1, v___x_792_);
lean_ctor_set(v___x_796_, 2, v___x_794_);
lean_ctor_set(v___x_796_, 3, v___x_795_);
v___x_797_ = l_Lean_Syntax_node1(v_a_745_, v___x_771_, v___x_756_);
v___x_798_ = l_Lean_Syntax_node2(v_a_745_, v___x_791_, v___x_796_, v___x_797_);
v___x_799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_745_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_Syntax_node3(v_a_745_, v___x_779_, v___x_790_, v___x_798_, v___x_800_);
lean_inc_ref_n(v___x_778_, 3);
v___x_802_ = l_Lean_Syntax_node2(v_a_745_, v___x_775_, v___x_778_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node1(v_a_745_, v___x_771_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node4(v_a_745_, v___x_773_, v___x_774_, v___x_803_, v___x_778_, v___x_778_);
v___x_805_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_745_);
lean_ctor_set(v___x_807_, 1, v___x_805_);
v___x_808_ = l_Lean_Syntax_node2(v_a_745_, v___x_806_, v___x_807_, v_fst_655_);
v___x_809_ = l_Lean_Syntax_node3(v_a_745_, v___x_771_, v___x_804_, v___x_778_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v_a_745_, v___x_770_, v___x_809_);
v___x_811_ = l_Lean_Syntax_node1(v_a_745_, v___x_769_, v___x_810_);
v___x_812_ = l_Lean_Syntax_node2(v_a_745_, v___x_766_, v___x_768_, v___x_811_);
v___x_813_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_745_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_817_ = l_Lean_addMacroScope(v_quotContext_746_, v___x_816_, v_currMacroScope_747_);
v___x_818_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_819_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_819_, 0, v_a_745_);
lean_ctor_set(v___x_819_, 1, v___x_815_);
lean_ctor_set(v___x_819_, 2, v___x_817_);
lean_ctor_set(v___x_819_, 3, v___x_818_);
v___x_820_ = l_Lean_Syntax_node8(v_a_745_, v___x_748_, v___x_750_, v___x_757_, v___x_759_, v___x_763_, v___x_765_, v___x_812_, v___x_814_, v___x_819_);
v___x_821_ = lean_box(v___x_689_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_821_);
lean_ctor_set(v___x_658_, 0, v___x_820_);
v___x_823_ = v___x_658_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_830_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_823_);
lean_ctor_set(v___x_653_, 0, v___x_683_);
v___x_825_ = v___x_653_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_825_);
lean_ctor_set(v___x_649_, 0, v___x_682_);
v___x_827_ = v___x_649_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v_a_639_ = v___x_827_;
goto v___jp_638_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_del_object(v___x_687_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_del_object(v___x_658_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_832_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_744_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_744_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
v___jp_840_:
{
uint8_t v___x_844_; 
v___x_844_ = lean_nat_dec_lt(v___y_842_, v___y_843_);
if (v___x_844_ == 0)
{
lean_dec(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
v_a_691_ = v___x_689_;
goto v___jp_690_;
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_usize_of_nat(v___y_842_);
lean_dec(v___y_842_);
v___x_846_ = lean_usize_of_nat(v___y_843_);
lean_dec(v___y_843_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_668_, v___y_841_, v___x_845_, v___x_846_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v___y_841_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; uint8_t v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
v_a_691_ = v___x_849_;
goto v___jp_690_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_del_object(v___x_687_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_850_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_847_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
v___jp_858_:
{
lean_object* v___x_861_; lean_object* v_array_862_; lean_object* v_start_863_; lean_object* v_stop_864_; uint8_t v___x_865_; 
lean_inc_ref(v_xs_626_);
v___x_861_ = l_Array_toSubarray___redArg(v_xs_626_, v_lower_859_, v_upper_860_);
v_array_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_array_862_);
v_start_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_start_863_);
v_stop_864_ = lean_ctor_get(v___x_861_, 2);
lean_inc(v_stop_864_);
lean_dec_ref(v___x_861_);
v___x_865_ = lean_nat_dec_lt(v_start_863_, v_stop_864_);
if (v___x_865_ == 0)
{
lean_dec(v_stop_864_);
lean_dec(v_start_863_);
lean_dec_ref(v_array_862_);
v_a_691_ = v___x_689_;
goto v___jp_690_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_array_862_);
v___x_867_ = lean_nat_dec_le(v_stop_864_, v___x_866_);
if (v___x_867_ == 0)
{
lean_dec(v_stop_864_);
v___y_841_ = v_array_862_;
v___y_842_ = v_start_863_;
v___y_843_ = v___x_866_;
goto v___jp_840_;
}
else
{
v___y_841_ = v_array_862_;
v___y_842_ = v_start_863_;
v___y_843_ = v_stop_864_;
goto v___jp_840_;
}
}
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v___x_681_);
lean_dec(v___x_680_);
lean_dec(v_a_679_);
lean_dec(v_a_677_);
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
if (v_isShared_659_ == 0)
{
v___x_917_ = v___x_658_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_656_);
v___x_917_ = v_reuseFailAlloc_924_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_917_);
lean_ctor_set(v___x_653_, 0, v___x_683_);
v___x_919_ = v___x_653_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_919_);
lean_ctor_set(v___x_649_, 0, v___x_682_);
v___x_921_ = v___x_649_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_a_639_ = v___x_921_;
goto v___jp_638_;
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_a_677_);
lean_dec(v_a_675_);
lean_dec(v_a_672_);
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_925_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_678_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_678_);
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
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_675_);
lean_dec(v_a_672_);
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_933_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_676_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_676_);
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
lean_dec(v_a_672_);
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_941_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_674_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_674_);
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
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_949_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_671_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_671_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v___x_667_);
lean_dec_ref(v_toConstantVal_660_);
v___x_957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_958_ = l_Lean_Core_mkFreshUserName(v___x_957_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc_n(v_a_961_, 3);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_Lean_mkIdent(v_a_959_);
lean_inc(v___x_962_);
v___x_963_ = lean_array_push(v_fst_647_, v___x_962_);
v___x_964_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67));
v___x_965_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v_a_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v_a_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_Syntax_node3(v_a_961_, v___x_964_, v___x_966_, v___x_962_, v___x_968_);
v___x_970_ = lean_array_push(v_fst_651_, v___x_969_);
if (v_isShared_659_ == 0)
{
v___x_972_ = v___x_658_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_snd_656_);
v___x_972_ = v_reuseFailAlloc_979_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_972_);
lean_ctor_set(v___x_653_, 0, v___x_970_);
v___x_974_ = v___x_653_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_974_);
lean_ctor_set(v___x_649_, 0, v___x_963_);
v___x_976_ = v___x_649_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v_a_639_ = v___x_976_;
goto v___jp_638_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_959_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_980_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_960_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_960_);
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
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_del_object(v___x_653_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_dec(v_a_629_);
lean_dec(v_auxFunName_628_);
lean_dec_ref(v_xs_626_);
lean_dec_ref(v_indVal_624_);
v_a_988_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_958_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_958_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_a_629_, v___x_640_);
lean_dec(v_a_629_);
v_a_629_ = v___x_641_;
v_b_630_ = v_a_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1001_, lean_object* v_indVal_1002_, lean_object* v___x_1003_, lean_object* v_xs_1004_, lean_object* v_a_1005_, lean_object* v_auxFunName_1006_, lean_object* v_a_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1001_, v_indVal_1002_, v___x_1003_, v_xs_1004_, v_a_1005_, v_auxFunName_1006_, v_a_1007_, v_b_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_a_1005_);
lean_dec(v___x_1003_);
lean_dec(v_upperBound_1001_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object* v_upperBound_1017_, lean_object* v_a_1018_, lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_nat_dec_lt(v_a_1018_, v_upperBound_1017_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_dec(v_a_1018_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_b_1019_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1052_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_fst_1033_ = lean_ctor_get(v_b_1019_, 0);
v_snd_1034_ = lean_ctor_get(v_b_1019_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_b_1019_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1036_ = v_b_1019_;
v_isShared_1037_ = v_isSharedCheck_1052_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_snd_1034_);
lean_inc(v_fst_1033_);
lean_dec(v_b_1019_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1052_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v_a_1030_);
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1030_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_1041_ = l_Lean_Syntax_node1(v_a_1030_, v___x_1040_, v___x_1039_);
v___x_1042_ = lean_array_push(v_fst_1033_, v___x_1041_);
lean_inc(v_a_1032_);
v___x_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_a_1032_);
lean_ctor_set(v___x_1043_, 1, v___x_1038_);
v___x_1044_ = l_Lean_Syntax_node1(v_a_1032_, v___x_1040_, v___x_1043_);
v___x_1045_ = lean_array_push(v_snd_1034_, v___x_1044_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1045_);
lean_ctor_set(v___x_1036_, 0, v___x_1042_);
v___x_1047_ = v___x_1036_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_nat_add(v_a_1018_, v___x_1048_);
lean_dec(v_a_1018_);
v_a_1018_ = v___x_1049_;
v_b_1019_ = v___x_1047_;
goto _start;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1030_);
lean_dec_ref(v_b_1019_);
lean_dec(v_a_1018_);
v_a_1053_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1031_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1031_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v_b_1019_);
lean_dec(v_a_1018_);
v_a_1061_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1029_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1029_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1069_, v_a_1070_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_upperBound_1069_);
return v_res_1079_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_1082_ = l_String_toRawSubstring_x27(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object* v_indVal_1101_, lean_object* v___x_1102_, lean_object* v_alts_1103_, lean_object* v_numFields_1104_, lean_object* v_auxFunName_1105_, lean_object* v___f_1106_, lean_object* v_head_1107_, lean_object* v_xs_1108_, lean_object* v_type_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Core_betaReduce(v_type_1109_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_numParams_1119_; lean_object* v_numIndices_1120_; lean_object* v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_numParams_1119_ = lean_ctor_get(v_indVal_1101_, 1);
lean_inc(v_numParams_1119_);
v_numIndices_1120_ = lean_ctor_get(v_indVal_1101_, 2);
lean_inc_ref(v_alts_1103_);
lean_inc(v___x_1102_);
v___x_1121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_1120_, v___x_1102_, v_alts_1103_, v___y_1114_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_ref_1123_; lean_object* v_quotContext_1124_; lean_object* v_currMacroScope_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_ref_1123_ = lean_ctor_get(v___y_1114_, 5);
v_quotContext_1124_ = lean_ctor_get(v___y_1114_, 10);
v_currMacroScope_1125_ = lean_ctor_get(v___y_1114_, 11);
v___x_1126_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_1127_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_1128_ = 0;
v___x_1129_ = l_Lean_SourceInfo_fromRef(v_ref_1123_, v___x_1128_);
lean_inc(v_currMacroScope_1125_);
lean_inc(v_quotContext_1124_);
v___x_1130_ = l_Lean_addMacroScope(v_quotContext_1124_, v___x_1127_, v_currMacroScope_1125_);
v___x_1131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_1132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1129_);
lean_ctor_set(v___x_1132_, 1, v___x_1126_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
v___x_1133_ = 1;
v___x_1134_ = lean_box(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1132_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
lean_inc_ref(v_alts_1103_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_alts_1103_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_alts_1103_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_inc(v___x_1102_);
v___x_1138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_numFields_1104_, v_indVal_1101_, v_numFields_1104_, v_xs_1108_, v_a_1118_, v_auxFunName_1105_, v___x_1102_, v___x_1137_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v_a_1118_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_snd_1140_; lean_object* v_snd_1141_; lean_object* v_fst_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1254_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v_snd_1140_ = lean_ctor_get(v_a_1139_, 1);
lean_inc(v_snd_1140_);
v_snd_1141_ = lean_ctor_get(v_snd_1140_, 1);
lean_inc(v_snd_1141_);
v_fst_1142_ = lean_ctor_get(v_a_1139_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_a_1139_, 1);
lean_dec(v_unused_1255_);
v___x_1144_ = v_a_1139_;
v_isShared_1145_ = v_isSharedCheck_1254_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_fst_1142_);
lean_dec(v_a_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1254_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1252_; 
v_fst_1146_ = lean_ctor_get(v_snd_1140_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_snd_1140_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_snd_1140_, 1);
lean_dec(v_unused_1253_);
v___x_1148_ = v_snd_1140_;
v_isShared_1149_ = v_isSharedCheck_1252_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_fst_1146_);
lean_dec(v_snd_1140_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1252_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1250_; 
v_fst_1150_ = lean_ctor_get(v_snd_1141_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v_snd_1141_, 1);
lean_dec(v_unused_1251_);
v___x_1152_ = v_snd_1141_;
v_isShared_1153_ = v_isSharedCheck_1250_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_fst_1150_);
lean_dec(v_snd_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1250_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_fst_1146_);
lean_ctor_set(v___x_1152_, 0, v_fst_1142_);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_fst_1142_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_fst_1146_);
v___x_1155_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_numParams_1119_, v___x_1102_, v___x_1155_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v_numParams_1119_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
lean_inc_ref(v___f_1106_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
v___x_1158_ = lean_apply_7(v___f_1106_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
lean_inc_ref(v___f_1106_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
v___x_1160_ = lean_apply_7(v___f_1106_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
v___x_1162_ = lean_apply_7(v___f_1106_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1216_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1216_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1216_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1215_; 
v_fst_1167_ = lean_ctor_get(v_a_1157_, 0);
v_snd_1168_ = lean_ctor_get(v_a_1157_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1170_ = v_a_1157_;
v_isShared_1171_ = v_isSharedCheck_1215_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_a_1157_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1215_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_1173_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_1159_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 2);
lean_ctor_set(v___x_1170_, 1, v___x_1173_);
lean_ctor_set(v___x_1170_, 0, v_a_1159_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = l_Lean_mkIdent(v_head_1107_);
lean_inc(v_a_1161_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 2);
lean_ctor_set(v___x_1148_, 1, v___x_1173_);
lean_ctor_set(v___x_1148_, 0, v_a_1161_);
v___x_1178_ = v___x_1148_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1161_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1173_);
v___x_1178_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1179_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
lean_inc(v___x_1176_);
lean_inc_n(v_a_1159_, 2);
v___x_1180_ = l_Lean_Syntax_node2(v_a_1159_, v___x_1179_, v___x_1175_, v___x_1176_);
lean_inc_n(v_a_1161_, 2);
v___x_1181_ = l_Lean_Syntax_node2(v_a_1161_, v___x_1179_, v___x_1178_, v___x_1176_);
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1183_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1184_ = l_Array_reverse___redArg(v_fst_1167_);
v___x_1185_ = l_Array_append___redArg(v___x_1183_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1186_, 0, v_a_1159_);
lean_ctor_set(v___x_1186_, 1, v___x_1182_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
v___x_1187_ = l_Array_reverse___redArg(v_snd_1168_);
v___x_1188_ = l_Array_append___redArg(v___x_1183_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1161_);
lean_ctor_set(v___x_1189_, 1, v___x_1182_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = l_Lean_Syntax_node2(v_a_1159_, v___x_1172_, v___x_1180_, v___x_1186_);
v___x_1191_ = lean_array_push(v_a_1122_, v___x_1190_);
v___x_1192_ = l_Lean_Syntax_node2(v_a_1161_, v___x_1172_, v___x_1181_, v___x_1189_);
v___x_1193_ = lean_array_push(v___x_1191_, v___x_1192_);
v___x_1194_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_1195_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc(v_a_1163_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 2);
lean_ctor_set(v___x_1144_, 1, v___x_1195_);
lean_ctor_set(v___x_1144_, 0, v_a_1163_);
v___x_1197_ = v___x_1144_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
size_t v_sz_1198_; size_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v_sz_1198_ = lean_array_size(v___x_1193_);
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1198_, v___x_1199_, v___x_1193_);
v___x_1201_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1202_ = l_Lean_mkSepArray(v___x_1200_, v___x_1201_);
lean_dec_ref(v___x_1200_);
v___x_1203_ = l_Array_append___redArg(v___x_1183_, v___x_1202_);
lean_dec_ref(v___x_1202_);
lean_inc_n(v_a_1163_, 3);
v___x_1204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1163_);
lean_ctor_set(v___x_1204_, 1, v___x_1182_);
lean_ctor_set(v___x_1204_, 2, v___x_1203_);
v___x_1205_ = l_Lean_Syntax_node1(v_a_1163_, v___x_1182_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1163_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node4(v_a_1163_, v___x_1194_, v___x_1197_, v___x_1205_, v___x_1207_, v_fst_1150_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1208_);
v___x_1210_ = v___x_1165_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1161_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1144_);
lean_dec(v_a_1122_);
lean_dec(v_head_1107_);
v_a_1217_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1162_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1162_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1144_);
lean_dec(v_a_1122_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
v_a_1225_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1160_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1160_);
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
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1157_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1144_);
lean_dec(v_a_1122_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
v_a_1233_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1158_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1158_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1144_);
lean_dec(v_a_1122_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
v_a_1241_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1156_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1156_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
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
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1122_);
lean_dec(v_numParams_1119_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
lean_dec(v___x_1102_);
v_a_1256_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1138_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1138_);
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
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_numParams_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_xs_1108_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
lean_dec(v_auxFunName_1105_);
lean_dec_ref(v_alts_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v_indVal_1101_);
v_a_1264_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1121_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1121_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_xs_1108_);
lean_dec(v_head_1107_);
lean_dec_ref(v___f_1106_);
lean_dec(v_auxFunName_1105_);
lean_dec_ref(v_alts_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v_indVal_1101_);
v_a_1272_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1117_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1117_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object* v_indVal_1280_, lean_object* v___x_1281_, lean_object* v_alts_1282_, lean_object* v_numFields_1283_, lean_object* v_auxFunName_1284_, lean_object* v___f_1285_, lean_object* v_head_1286_, lean_object* v_xs_1287_, lean_object* v_type_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(v_indVal_1280_, v___x_1281_, v_alts_1282_, v_numFields_1283_, v_auxFunName_1284_, v___f_1285_, v_head_1286_, v_xs_1287_, v_type_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v_numFields_1283_);
return v_res_1296_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_instMonadEIO(lean_box(0));
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_toApplicative_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1405_; 
v___x_1312_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_1313_ = l_StateRefT_x27_instMonad___redArg(v___x_1312_);
v_toApplicative_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1313_, 1);
lean_dec(v_unused_1406_);
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1405_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_toApplicative_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1405_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_toFunctor_1318_; lean_object* v_toSeq_1319_; lean_object* v_toSeqLeft_1320_; lean_object* v_toSeqRight_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1403_; 
v_toFunctor_1318_ = lean_ctor_get(v_toApplicative_1314_, 0);
v_toSeq_1319_ = lean_ctor_get(v_toApplicative_1314_, 2);
v_toSeqLeft_1320_ = lean_ctor_get(v_toApplicative_1314_, 3);
v_toSeqRight_1321_ = lean_ctor_get(v_toApplicative_1314_, 4);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_toApplicative_1314_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_toApplicative_1314_, 1);
lean_dec(v_unused_1404_);
v___x_1323_ = v_toApplicative_1314_;
v_isShared_1324_ = v_isSharedCheck_1403_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_toSeqRight_1321_);
lean_inc(v_toSeqLeft_1320_);
lean_inc(v_toSeq_1319_);
lean_inc(v_toFunctor_1318_);
lean_dec(v_toApplicative_1314_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1403_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___x_1334_; 
v___f_1325_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_1326_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1318_);
v___f_1327_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1327_, 0, v_toFunctor_1318_);
v___f_1328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1328_, 0, v_toFunctor_1318_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___f_1327_);
lean_ctor_set(v___x_1329_, 1, v___f_1328_);
v___f_1330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1330_, 0, v_toSeqRight_1321_);
v___f_1331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1331_, 0, v_toSeqLeft_1320_);
v___f_1332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1332_, 0, v_toSeq_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v___f_1330_);
lean_ctor_set(v___x_1323_, 3, v___f_1331_);
lean_ctor_set(v___x_1323_, 2, v___f_1332_);
lean_ctor_set(v___x_1323_, 1, v___f_1325_);
lean_ctor_set(v___x_1323_, 0, v___x_1329_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___f_1325_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v___f_1332_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v___f_1331_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v___f_1330_);
v___x_1334_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___f_1326_);
lean_ctor_set(v___x_1316_, 0, v___x_1334_);
v___x_1336_ = v___x_1316_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___f_1326_);
v___x_1336_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v_toApplicative_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1399_; 
v___x_1337_ = l_StateRefT_x27_instMonad___redArg(v___x_1336_);
v_toApplicative_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1400_);
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1399_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_toApplicative_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1399_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_toFunctor_1342_; lean_object* v_toSeq_1343_; lean_object* v_toSeqLeft_1344_; lean_object* v_toSeqRight_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1397_; 
v_toFunctor_1342_ = lean_ctor_get(v_toApplicative_1338_, 0);
v_toSeq_1343_ = lean_ctor_get(v_toApplicative_1338_, 2);
v_toSeqLeft_1344_ = lean_ctor_get(v_toApplicative_1338_, 3);
v_toSeqRight_1345_ = lean_ctor_get(v_toApplicative_1338_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_toApplicative_1338_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_dec(v_unused_1398_);
v___x_1347_ = v_toApplicative_1338_;
v_isShared_1348_ = v_isSharedCheck_1397_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_toSeqRight_1345_);
lean_inc(v_toSeqLeft_1344_);
lean_inc(v_toSeq_1343_);
lean_inc(v_toFunctor_1342_);
lean_dec(v_toApplicative_1338_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1397_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___f_1349_; lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1358_; 
v___f_1349_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1350_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1342_);
v___f_1351_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1351_, 0, v_toFunctor_1342_);
v___f_1352_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1352_, 0, v_toFunctor_1342_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___f_1351_);
lean_ctor_set(v___x_1353_, 1, v___f_1352_);
v___f_1354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1354_, 0, v_toSeqRight_1345_);
v___f_1355_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1355_, 0, v_toSeqLeft_1344_);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1356_, 0, v_toSeq_1343_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 4, v___f_1354_);
lean_ctor_set(v___x_1347_, 3, v___f_1355_);
lean_ctor_set(v___x_1347_, 2, v___f_1356_);
lean_ctor_set(v___x_1347_, 1, v___f_1349_);
lean_ctor_set(v___x_1347_, 0, v___x_1353_);
v___x_1358_ = v___x_1347_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___f_1349_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v___f_1356_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v___f_1355_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v___f_1354_);
v___x_1358_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___f_1350_);
lean_ctor_set(v___x_1340_, 0, v___x_1358_);
v___x_1360_ = v___x_1340_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___f_1350_);
v___x_1360_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v_toApplicative_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1393_; 
v___x_1361_ = l_StateRefT_x27_instMonad___redArg(v___x_1360_);
v_toApplicative_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1361_, 1);
lean_dec(v_unused_1394_);
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1393_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_toApplicative_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1393_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_toFunctor_1366_; lean_object* v_toSeq_1367_; lean_object* v_toSeqLeft_1368_; lean_object* v_toSeqRight_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1391_; 
v_toFunctor_1366_ = lean_ctor_get(v_toApplicative_1362_, 0);
v_toSeq_1367_ = lean_ctor_get(v_toApplicative_1362_, 2);
v_toSeqLeft_1368_ = lean_ctor_get(v_toApplicative_1362_, 3);
v_toSeqRight_1369_ = lean_ctor_get(v_toApplicative_1362_, 4);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_toApplicative_1362_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v_toApplicative_1362_, 1);
lean_dec(v_unused_1392_);
v___x_1371_ = v_toApplicative_1362_;
v_isShared_1372_ = v_isSharedCheck_1391_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_toSeqRight_1369_);
lean_inc(v_toSeqLeft_1368_);
lean_inc(v_toSeq_1367_);
lean_inc(v_toFunctor_1366_);
lean_dec(v_toApplicative_1362_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1391_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___f_1380_; lean_object* v___x_1382_; 
v___f_1373_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1374_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1366_);
v___f_1375_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1375_, 0, v_toFunctor_1366_);
v___f_1376_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1376_, 0, v_toFunctor_1366_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___f_1375_);
lean_ctor_set(v___x_1377_, 1, v___f_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1378_, 0, v_toSeqRight_1369_);
v___f_1379_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1379_, 0, v_toSeqLeft_1368_);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toSeq_1367_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___f_1378_);
lean_ctor_set(v___x_1371_, 3, v___f_1379_);
lean_ctor_set(v___x_1371_, 2, v___f_1380_);
lean_ctor_set(v___x_1371_, 1, v___f_1373_);
lean_ctor_set(v___x_1371_, 0, v___x_1377_);
v___x_1382_ = v___x_1371_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___f_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___f_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v___f_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___f_1378_);
v___x_1382_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___f_1374_);
lean_ctor_set(v___x_1364_, 0, v___x_1382_);
v___x_1384_ = v___x_1364_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___f_1374_);
v___x_1384_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_49126__overap_1387_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_instInhabitedOfMonad___redArg(v___x_1384_, v___x_1385_);
v___x_49126__overap_1387_ = lean_panic_fn_borrowed(v___x_1386_, v_msg_1304_);
lean_dec(v___x_1386_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
v___x_1388_ = lean_apply_7(v___x_49126__overap_1387_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, lean_box(0));
return v___x_1388_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_1416_, lean_object* v_opt_1417_){
_start:
{
lean_object* v_name_1418_; lean_object* v_defValue_1419_; lean_object* v_map_1420_; lean_object* v___x_1421_; 
v_name_1418_ = lean_ctor_get(v_opt_1417_, 0);
v_defValue_1419_ = lean_ctor_get(v_opt_1417_, 1);
v_map_1420_ = lean_ctor_get(v_opts_1416_, 0);
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1420_, v_name_1418_);
if (lean_obj_tag(v___x_1421_) == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_unbox(v_defValue_1419_);
return v___x_1422_;
}
else
{
lean_object* v_val_1423_; 
v_val_1423_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___x_1421_, 1);
if (lean_obj_tag(v_val_1423_) == 1)
{
uint8_t v_v_1424_; 
v_v_1424_ = lean_ctor_get_uint8(v_val_1423_, 0);
lean_dec_ref_known(v_val_1423_, 0);
return v_v_1424_;
}
else
{
uint8_t v___x_1425_; 
lean_dec(v_val_1423_);
v___x_1425_ = lean_unbox(v_defValue_1419_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_1426_, lean_object* v_opt_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_1426_, v_opt_1427_);
lean_dec_ref(v_opt_1427_);
lean_dec_ref(v_opts_1426_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_box(1);
v___x_1431_ = l_Lean_MessageData_ofFormat(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_1436_ = l_Lean_MessageData_ofFormat(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 0)
{
return v_x_1437_;
}
else
{
lean_object* v_head_1439_; lean_object* v_tail_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1462_; 
v_head_1439_ = lean_ctor_get(v_x_1438_, 0);
v_tail_1440_ = lean_ctor_get(v_x_1438_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1438_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1442_ = v_x_1438_;
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_tail_1440_);
lean_inc(v_head_1439_);
lean_dec(v_x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_before_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1460_; 
v_before_1444_ = lean_ctor_get(v_head_1439_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_head_1439_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_head_1439_, 1);
lean_dec(v_unused_1461_);
v___x_1446_ = v_head_1439_;
v_isShared_1447_ = v_isSharedCheck_1460_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_before_1444_);
lean_dec(v_head_1439_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1460_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 7);
lean_ctor_set(v___x_1446_, 1, v___x_1448_);
lean_ctor_set(v___x_1446_, 0, v_x_1437_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_x_1437_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 7);
lean_ctor_set(v___x_1442_, 1, v___x_1451_);
lean_ctor_set(v___x_1442_, 0, v___x_1450_);
v___x_1453_ = v___x_1442_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = l_Lean_MessageData_ofSyntax(v_before_1444_);
v___x_1455_ = l_Lean_indentD(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v_x_1437_ = v___x_1456_;
v_x_1438_ = v_tail_1440_;
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
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1467_ = l_Lean_MessageData_ofFormat(v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1468_, lean_object* v_macroStack_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_options_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; uint8_t v___x_1475_; 
v_options_1472_ = lean_ctor_get(v___y_1470_, 2);
v___x_1473_ = l_Lean_Elab_pp_macroStack;
v___x_1474_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_1472_, v___x_1473_);
v___x_1475_ = lean_bool_not(v___x_1474_);
if (v___x_1475_ == 0)
{
if (lean_obj_tag(v_macroStack_1469_) == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_msgData_1468_);
return v___x_1476_;
}
else
{
lean_object* v_head_1477_; lean_object* v_after_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1493_; 
v_head_1477_ = lean_ctor_get(v_macroStack_1469_, 0);
lean_inc(v_head_1477_);
v_after_1478_ = lean_ctor_get(v_head_1477_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_head_1477_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_head_1477_, 0);
lean_dec(v_unused_1494_);
v___x_1480_ = v_head_1477_;
v_isShared_1481_ = v_isSharedCheck_1493_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_after_1478_);
lean_dec(v_head_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1493_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 7);
lean_ctor_set(v___x_1480_, 1, v___x_1482_);
lean_ctor_set(v___x_1480_, 0, v_msgData_1468_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_msgData_1468_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_msgData_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1485_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_MessageData_ofSyntax(v_after_1478_);
v___x_1488_ = l_Lean_indentD(v___x_1487_);
v_msgData_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1489_, 0, v___x_1486_);
lean_ctor_set(v_msgData_1489_, 1, v___x_1488_);
v___x_1490_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_1489_, v_macroStack_1469_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
}
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_macroStack_1469_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_msgData_1468_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1496_, lean_object* v_macroStack_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1496_, v_macroStack_1497_, v___y_1498_);
lean_dec_ref(v___y_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v_env_1508_; lean_object* v___x_1509_; lean_object* v_mctx_1510_; lean_object* v_lctx_1511_; lean_object* v_options_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1507_ = lean_st_ref_get(v___y_1505_);
v_env_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc_ref(v_env_1508_);
lean_dec(v___x_1507_);
v___x_1509_ = lean_st_ref_get(v___y_1503_);
v_mctx_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_mctx_1510_);
lean_dec(v___x_1509_);
v_lctx_1511_ = lean_ctor_get(v___y_1502_, 2);
v_options_1512_ = lean_ctor_get(v___y_1504_, 2);
lean_inc_ref(v_options_1512_);
lean_inc_ref(v_lctx_1511_);
v___x_1513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1513_, 0, v_env_1508_);
lean_ctor_set(v___x_1513_, 1, v_mctx_1510_);
lean_ctor_set(v___x_1513_, 2, v_lctx_1511_);
lean_ctor_set(v___x_1513_, 3, v_options_1512_);
v___x_1514_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_msgData_1501_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_ref_1531_; lean_object* v___x_1532_; lean_object* v_a_1533_; lean_object* v_macroStack_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_ref_1531_ = lean_ctor_get(v___y_1528_, 5);
v___x_1532_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1523_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v_macroStack_1534_ = lean_ctor_get(v___y_1524_, 1);
v___x_1535_ = l_Lean_Elab_getBetterRef(v_ref_1531_, v_macroStack_1534_);
lean_inc(v_macroStack_1534_);
v___x_1536_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1533_, v_macroStack_1534_, v___y_1528_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1535_);
lean_ctor_set(v___x_1541_, 1, v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1564_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1565_ = lean_unsigned_to_nat(11u);
v___x_1566_ = lean_unsigned_to_nat(122u);
v___x_1567_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1568_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1569_ = l_mkPanicMessageWithDecl(v___x_1568_, v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1586_; lean_object* v_env_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = lean_st_ref_get(v___y_1576_);
v_env_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_env_1587_);
lean_dec(v___x_1586_);
v___x_1588_ = 0;
lean_inc(v_constName_1570_);
v___x_1589_ = l_Lean_Environment_findAsync_x3f(v_env_1587_, v_constName_1570_, v___x_1588_);
if (lean_obj_tag(v___x_1589_) == 1)
{
lean_object* v_val_1590_; uint8_t v_kind_1591_; 
v_val_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v_kind_1591_ = lean_ctor_get_uint8(v_val_1590_, sizeof(void*)*3);
if (v_kind_1591_ == 6)
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1590_);
if (lean_obj_tag(v___x_1592_) == 6)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_constName_1570_);
v_val_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 0);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_val_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___x_1592_);
v___x_1601_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1602_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1601_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1611_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
if (lean_obj_tag(v_a_1603_) == 0)
{
lean_del_object(v___x_1605_);
goto v___jp_1578_;
}
else
{
lean_object* v_val_1607_; lean_object* v___x_1609_; 
lean_dec(v_constName_1570_);
v_val_1607_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v_a_1603_, 1);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_val_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_val_1607_);
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
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_constName_1570_);
v_a_1612_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1602_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1602_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_dec(v_val_1590_);
goto v___jp_1578_;
}
}
else
{
lean_dec(v___x_1589_);
goto v___jp_1578_;
}
v___jp_1578_:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1579_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1580_ = 0;
v___x_1581_ = l_Lean_MessageData_ofConstName(v_constName_1570_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1579_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1584_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_constName_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_indVal_1630_, lean_object* v_auxFunName_1631_, lean_object* v_as_x27_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
if (lean_obj_tag(v_as_x27_1632_) == 0)
{
lean_object* v___x_1641_; 
lean_dec(v_auxFunName_1631_);
lean_dec_ref(v_indVal_1630_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_b_1633_);
return v___x_1641_;
}
else
{
lean_object* v_head_1642_; lean_object* v_tail_1643_; lean_object* v___x_1644_; 
v_head_1642_ = lean_ctor_get(v_as_x27_1632_, 0);
v_tail_1643_ = lean_ctor_get(v_as_x27_1632_, 1);
lean_inc(v_head_1642_);
v___x_1644_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_head_1642_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v_toConstantVal_1646_; lean_object* v_numFields_1647_; lean_object* v_type_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; lean_object* v_alts_1651_; lean_object* v___f_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v_toConstantVal_1646_ = lean_ctor_get(v_a_1645_, 0);
lean_inc_ref(v_toConstantVal_1646_);
v_numFields_1647_ = lean_ctor_get(v_a_1645_, 4);
lean_inc(v_numFields_1647_);
lean_dec(v_a_1645_);
v_type_1648_ = lean_ctor_get(v_toConstantVal_1646_, 2);
lean_inc_ref(v_type_1648_);
lean_dec_ref(v_toConstantVal_1646_);
v___f_1649_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_1650_ = lean_unsigned_to_nat(0u);
v_alts_1651_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc(v_head_1642_);
lean_inc(v_auxFunName_1631_);
lean_inc_ref(v_indVal_1630_);
v___f_1652_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1652_, 0, v_indVal_1630_);
lean_closure_set(v___f_1652_, 1, v___x_1650_);
lean_closure_set(v___f_1652_, 2, v_alts_1651_);
lean_closure_set(v___f_1652_, 3, v_numFields_1647_);
lean_closure_set(v___f_1652_, 4, v_auxFunName_1631_);
lean_closure_set(v___f_1652_, 5, v___f_1649_);
lean_closure_set(v___f_1652_, 6, v_head_1642_);
v___x_1653_ = 0;
v___x_1654_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_1648_, v___f_1652_, v___x_1653_, v___x_1653_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = lean_array_push(v_b_1633_, v_a_1655_);
v_as_x27_1632_ = v_tail_1643_;
v_b_1633_ = v___x_1656_;
goto _start;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_b_1633_);
lean_dec(v_auxFunName_1631_);
lean_dec_ref(v_indVal_1630_);
v_a_1658_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1654_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_b_1633_);
lean_dec(v_auxFunName_1631_);
lean_dec_ref(v_indVal_1630_);
v_a_1666_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1644_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1644_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1674_, lean_object* v_auxFunName_1675_, lean_object* v_as_x27_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1674_, v_auxFunName_1675_, v_as_x27_1676_, v_b_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_as_x27_1676_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_bs_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_lt(v_i_1687_, v_sz_1686_);
if (v___x_1689_ == 0)
{
return v_bs_1688_;
}
else
{
lean_object* v_v_1690_; lean_object* v___x_1691_; lean_object* v_bs_x27_1692_; size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; 
v_v_1690_ = lean_array_uget(v_bs_1688_, v_i_1687_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v_bs_x27_1692_ = lean_array_uset(v_bs_1688_, v_i_1687_, v___x_1691_);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_add(v_i_1687_, v___x_1693_);
v___x_1695_ = lean_array_uset(v_bs_x27_1692_, v_i_1687_, v_v_1690_);
v_i_1687_ = v___x_1694_;
v_bs_1688_ = v___x_1695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1697_, lean_object* v_i_1698_, lean_object* v_bs_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1697_);
lean_dec(v_sz_1697_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1700_, v_i_boxed_1701_, v_bs_1699_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object* v_indVal_1703_, lean_object* v_auxFunName_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_ctors_1712_; lean_object* v_alts_1713_; lean_object* v___x_1714_; 
v_ctors_1712_ = lean_ctor_get(v_indVal_1703_, 4);
v_alts_1713_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc_ref(v_indVal_1703_);
v___x_1714_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1703_, v_auxFunName_1704_, v_ctors_1712_, v_alts_1713_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_1703_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec_ref(v_indVal_1703_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1728_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1728_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1728_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; size_t v_sz_1722_; size_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1721_ = lean_array_push(v_a_1715_, v_a_1717_);
v_sz_1722_ = lean_array_size(v___x_1721_);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_1722_, v___x_1723_, v___x_1721_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1715_);
v_a_1729_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1716_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1716_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_dec_ref(v_indVal_1703_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1737_, lean_object* v_auxFunName_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1737_, v_auxFunName_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object* v_upperBound_1747_, lean_object* v_inst_1748_, lean_object* v_R_1749_, lean_object* v_a_1750_, lean_object* v_b_1751_, lean_object* v_c_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1747_, v_a_1750_, v_b_1751_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_upperBound_1761_, lean_object* v_inst_1762_, lean_object* v_R_1763_, lean_object* v_a_1764_, lean_object* v_b_1765_, lean_object* v_c_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(v_upperBound_1761_, v_inst_1762_, v_R_1763_, v_a_1764_, v_b_1765_, v_c_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v_upperBound_1761_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object* v___x_1775_, lean_object* v_as_1776_, size_t v_i_1777_, size_t v_stop_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_1775_, v_as_1776_, v_i_1777_, v_stop_1778_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v___x_1787_, lean_object* v_as_1788_, lean_object* v_i_1789_, lean_object* v_stop_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
size_t v_i_boxed_1798_; size_t v_stop_boxed_1799_; lean_object* v_res_1800_; 
v_i_boxed_1798_ = lean_unbox_usize(v_i_1789_);
lean_dec(v_i_1789_);
v_stop_boxed_1799_ = lean_unbox_usize(v_stop_1790_);
lean_dec(v_stop_1790_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(v___x_1787_, v_as_1788_, v_i_boxed_1798_, v_stop_boxed_1799_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v_as_1788_);
lean_dec_ref(v___x_1787_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1801_, lean_object* v_indVal_1802_, lean_object* v___x_1803_, lean_object* v_xs_1804_, lean_object* v_a_1805_, lean_object* v_auxFunName_1806_, lean_object* v_inst_1807_, lean_object* v_R_1808_, lean_object* v_a_1809_, lean_object* v_b_1810_, lean_object* v_c_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1801_, v_indVal_1802_, v___x_1803_, v_xs_1804_, v_a_1805_, v_auxFunName_1806_, v_a_1809_, v_b_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1820_ = _args[0];
lean_object* v_indVal_1821_ = _args[1];
lean_object* v___x_1822_ = _args[2];
lean_object* v_xs_1823_ = _args[3];
lean_object* v_a_1824_ = _args[4];
lean_object* v_auxFunName_1825_ = _args[5];
lean_object* v_inst_1826_ = _args[6];
lean_object* v_R_1827_ = _args[7];
lean_object* v_a_1828_ = _args[8];
lean_object* v_b_1829_ = _args[9];
lean_object* v_c_1830_ = _args[10];
lean_object* v___y_1831_ = _args[11];
lean_object* v___y_1832_ = _args[12];
lean_object* v___y_1833_ = _args[13];
lean_object* v___y_1834_ = _args[14];
lean_object* v___y_1835_ = _args[15];
lean_object* v___y_1836_ = _args[16];
lean_object* v___y_1837_ = _args[17];
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(v_upperBound_1820_, v_indVal_1821_, v___x_1822_, v_xs_1823_, v_a_1824_, v_auxFunName_1825_, v_inst_1826_, v_R_1827_, v_a_1828_, v_b_1829_, v_c_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v_a_1824_);
lean_dec(v___x_1822_);
lean_dec(v_upperBound_1820_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object* v_indVal_1839_, lean_object* v_auxFunName_1840_, lean_object* v_as_1841_, lean_object* v_as_x27_1842_, lean_object* v_b_1843_, lean_object* v_a_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1839_, v_auxFunName_1840_, v_as_x27_1842_, v_b_1843_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_indVal_1853_, lean_object* v_auxFunName_1854_, lean_object* v_as_1855_, lean_object* v_as_x27_1856_, lean_object* v_b_1857_, lean_object* v_a_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(v_indVal_1853_, v_auxFunName_1854_, v_as_1855_, v_as_x27_1856_, v_b_1857_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_as_x27_1856_);
lean_dec(v_as_1855_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1867_, lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1877_, v_msg_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1887_, lean_object* v_macroStack_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1887_, v_macroStack_1888_, v___y_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1897_, lean_object* v_macroStack_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1897_, v_macroStack_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object* v_header_1920_, lean_object* v_indVal_1921_, lean_object* v_auxFunName_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1930_; 
lean_inc_ref(v_indVal_1921_);
v___x_1930_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1920_, v_indVal_1921_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1921_, v_auxFunName_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1963_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1963_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1963_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_ref_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; size_t v_sz_1946_; size_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v_ref_1937_ = lean_ctor_get(v_a_1927_, 5);
v___x_1938_ = 0;
v___x_1939_ = l_Lean_SourceInfo_fromRef(v_ref_1937_, v___x_1938_);
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_1941_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_1939_, 6);
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1939_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
v___x_1943_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1944_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1939_);
lean_ctor_set(v___x_1945_, 1, v___x_1943_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
v_sz_1946_ = lean_array_size(v_a_1931_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1946_, v___x_1947_, v_a_1931_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1950_ = l_Lean_mkSepArray(v___x_1948_, v___x_1949_);
lean_dec_ref(v___x_1948_);
v___x_1951_ = l_Array_append___redArg(v___x_1944_, v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1939_);
lean_ctor_set(v___x_1952_, 1, v___x_1943_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
v___x_1953_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_1954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1939_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_1956_ = l_Array_append___redArg(v___x_1944_, v_a_1933_);
lean_dec(v_a_1933_);
v___x_1957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1939_);
lean_ctor_set(v___x_1957_, 1, v___x_1943_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
v___x_1958_ = l_Lean_Syntax_node1(v___x_1939_, v___x_1955_, v___x_1957_);
lean_inc_ref(v___x_1945_);
v___x_1959_ = l_Lean_Syntax_node6(v___x_1939_, v___x_1941_, v___x_1942_, v___x_1945_, v___x_1945_, v___x_1952_, v___x_1954_, v___x_1958_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1959_);
v___x_1961_ = v___x_1935_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_a_1931_);
v_a_1964_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1932_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1932_);
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
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_auxFunName_1922_);
lean_dec_ref(v_indVal_1921_);
v_a_1972_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1930_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1930_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object* v_header_1980_, lean_object* v_indVal_1981_, lean_object* v_auxFunName_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_1980_, v_indVal_1981_, v_auxFunName_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
return v_res_1990_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_44443__overap_2001_; lean_object* v___x_2002_; 
v___x_2000_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0);
v___x_44443__overap_2001_ = lean_panic_fn_borrowed(v___x_2000_, v_msg_1992_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
v___x_2002_ = lean_apply_7(v___x_44443__overap_2001_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, lean_box(0));
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v_msg_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object* v___x_2012_, lean_object* v_as_2013_, size_t v_i_2014_, size_t v_stop_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_eq(v_i_2014_, v_stop_2015_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_array_uget_borrowed(v_as_2013_, v_i_2014_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___x_2022_);
v___x_2023_ = lean_infer_type(v___x_2022_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2036_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_containsFVar(v_a_2024_, v___x_2012_);
lean_dec(v_a_2024_);
if (v___x_2028_ == 0)
{
size_t v___x_2029_; size_t v___x_2030_; 
lean_del_object(v___x_2026_);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2014_, v___x_2029_);
v_i_2014_ = v___x_2030_;
goto _start;
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_box(v___x_2028_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2032_);
v___x_2034_ = v___x_2026_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
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
v_a_2037_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2023_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2023_);
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
else
{
uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = 0;
v___x_2046_ = lean_box(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object* v___x_2048_, lean_object* v_as_2049_, lean_object* v_i_2050_, lean_object* v_stop_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
size_t v_i_boxed_2057_; size_t v_stop_boxed_2058_; lean_object* v_res_2059_; 
v_i_boxed_2057_ = lean_unbox_usize(v_i_2050_);
lean_dec(v_i_2050_);
v_stop_boxed_2058_ = lean_unbox_usize(v_stop_2051_);
lean_dec(v_stop_2051_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2048_, v_as_2049_, v_i_boxed_2057_, v_stop_boxed_2058_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec_ref(v_as_2049_);
lean_dec(v___x_2048_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object* v_upperBound_2061_, lean_object* v_indVal_2062_, lean_object* v___x_2063_, lean_object* v_xs_2064_, lean_object* v_a_2065_, lean_object* v___x_2066_, lean_object* v_auxFunName_2067_, lean_object* v_a_2068_, lean_object* v_b_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_nat_dec_lt(v_a_2068_, v_upperBound_2061_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_b_2069_);
return v___x_2078_;
}
else
{
lean_object* v_snd_2079_; lean_object* v_snd_2080_; lean_object* v_fst_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2422_; 
v_snd_2079_ = lean_ctor_get(v_b_2069_, 1);
lean_inc(v_snd_2079_);
v_snd_2080_ = lean_ctor_get(v_snd_2079_, 1);
lean_inc(v_snd_2080_);
v_fst_2081_ = lean_ctor_get(v_b_2069_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_b_2069_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v_b_2069_, 1);
lean_dec(v_unused_2423_);
v___x_2083_ = v_b_2069_;
v_isShared_2084_ = v_isSharedCheck_2422_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_fst_2081_);
lean_dec(v_b_2069_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2422_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_fst_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2420_; 
v_fst_2085_ = lean_ctor_get(v_snd_2079_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_snd_2079_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_snd_2079_, 1);
lean_dec(v_unused_2421_);
v___x_2087_ = v_snd_2079_;
v_isShared_2088_ = v_isSharedCheck_2420_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_fst_2085_);
lean_dec(v_snd_2079_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2420_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_fst_2089_; lean_object* v_snd_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2419_; 
v_fst_2089_ = lean_ctor_get(v_snd_2080_, 0);
v_snd_2090_ = lean_ctor_get(v_snd_2080_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_snd_2080_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2092_ = v_snd_2080_;
v_isShared_2093_ = v_isSharedCheck_2419_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snd_2090_);
lean_inc(v_fst_2089_);
lean_dec(v_snd_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2419_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_numParams_2094_; lean_object* v___x_2095_; lean_object* v_a_2097_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_numParams_2094_ = lean_ctor_get(v_indVal_2062_, 1);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_numParams_2094_, v___x_2063_);
v___x_2101_ = lean_nat_sub(v___x_2100_, v_a_2068_);
lean_dec(v___x_2100_);
v___x_2102_ = lean_nat_sub(v___x_2101_, v___x_2095_);
lean_dec(v___x_2101_);
v___x_2103_ = l_Lean_instInhabitedExpr;
v___x_2104_ = lean_array_get_borrowed(v___x_2103_, v_xs_2064_, v___x_2102_);
v___x_2105_ = l_Lean_Expr_fvarId_x21(v___x_2104_);
v___x_2106_ = l_Lean_Expr_containsFVar(v_a_2065_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_inc(v___x_2105_);
v___x_2107_ = l_Lean_FVarId_getUserName___redArg(v___x_2105_, v___y_2072_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_n(v_a_2108_, 2);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Core_mkFreshUserName(v_a_2108_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0));
v___x_2112_ = lean_name_append_after(v_a_2108_, v___x_2111_);
v___x_2113_ = l_Lean_Core_mkFreshUserName(v___x_2112_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___x_2104_);
v___x_2115_ = lean_infer_type(v___x_2104_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_n(v_a_2116_, 2);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2117_ = l_Lean_Meta_isProp(v_a_2116_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_mkIdent(v_a_2110_);
v___x_2120_ = l_Lean_mkIdent(v_a_2114_);
lean_inc(v___x_2119_);
v___x_2121_ = lean_array_push(v_fst_2081_, v___x_2119_);
lean_inc(v___x_2120_);
v___x_2122_ = lean_array_push(v_fst_2085_, v___x_2120_);
v___x_2123_ = lean_unbox(v_a_2118_);
if (v___x_2123_ == 0)
{
uint8_t v___x_2124_; uint8_t v_a_2126_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v_lower_2292_; lean_object* v_upper_2293_; 
v___x_2124_ = l_Lean_Expr_isAppOf(v_a_2116_, v___x_2066_);
lean_dec(v_a_2116_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
lean_dec(v_a_2118_);
v___x_2301_ = lean_nat_add(v___x_2102_, v___x_2095_);
lean_dec(v___x_2102_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_array_get_size(v_xs_2064_);
v___x_2304_ = lean_nat_dec_le(v___x_2301_, v___x_2302_);
if (v___x_2304_ == 0)
{
v_lower_2292_ = v___x_2301_;
v_upper_2293_ = v___x_2303_;
goto v___jp_2291_;
}
else
{
lean_dec(v___x_2301_);
v_lower_2292_ = v___x_2302_;
v_upper_2293_ = v___x_2303_;
goto v___jp_2291_;
}
}
else
{
uint8_t v___x_2305_; 
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2083_);
v___x_2305_ = lean_unbox(v_snd_2090_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
lean_dec(v_a_2118_);
v___x_2306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_n(v_a_2307_, 4);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2067_);
v___x_2310_ = l_Lean_mkIdent(v_auxFunName_2067_);
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2312_ = l_Lean_Syntax_node2(v_a_2307_, v___x_2311_, v___x_2119_, v___x_2120_);
v___x_2313_ = l_Lean_Syntax_node2(v_a_2307_, v___x_2309_, v___x_2310_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2307_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node3(v_a_2307_, v___x_2308_, v___x_2313_, v___x_2315_, v_fst_2089_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_snd_2090_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2122_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2121_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v_a_2097_ = v___x_2319_;
goto v___jp_2096_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2320_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2306_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2306_);
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
lean_object* v___x_2328_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
v___x_2328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_n(v_a_2329_, 2);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2067_);
v___x_2331_ = l_Lean_mkIdent(v_auxFunName_2067_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2333_ = l_Lean_Syntax_node2(v_a_2329_, v___x_2332_, v___x_2119_, v___x_2120_);
v___x_2334_ = l_Lean_Syntax_node2(v_a_2329_, v___x_2330_, v___x_2331_, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_a_2118_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2122_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2121_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v_a_2097_ = v___x_2337_;
goto v___jp_2096_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_dec(v_a_2118_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2338_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2328_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2328_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
v___jp_2125_:
{
if (v_a_2126_ == 0)
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_unbox(v_snd_2090_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_n(v_a_2129_, 4);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2131_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2132_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_a_2129_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_Syntax_node3(v_a_2129_, v___x_2131_, v___x_2119_, v___x_2133_, v___x_2120_);
v___x_2135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v_a_2129_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node3(v_a_2129_, v___x_2130_, v___x_2134_, v___x_2136_, v_fst_2089_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2137_);
v___x_2139_ = v___x_2092_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_snd_2090_);
v___x_2139_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2139_);
lean_ctor_set(v___x_2087_, 0, v___x_2122_);
v___x_2141_ = v___x_2087_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2141_);
lean_ctor_set(v___x_2083_, 0, v___x_2121_);
v___x_2143_ = v___x_2083_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
v_a_2097_ = v___x_2143_;
goto v___jp_2096_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2083_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2147_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2128_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2128_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v___x_2155_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
v___x_2155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc_n(v_a_2156_, 2);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_a_2156_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node3(v_a_2156_, v___x_2157_, v___x_2119_, v___x_2159_, v___x_2120_);
v___x_2161_ = lean_box(v_a_2126_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2161_);
lean_ctor_set(v___x_2092_, 0, v___x_2160_);
v___x_2163_ = v___x_2092_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2163_);
lean_ctor_set(v___x_2087_, 0, v___x_2122_);
v___x_2165_ = v___x_2087_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2165_);
lean_ctor_set(v___x_2083_, 0, v___x_2121_);
v___x_2167_ = v___x_2083_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v_a_2097_ = v___x_2167_;
goto v___jp_2096_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_del_object(v___x_2092_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2083_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2171_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2155_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2155_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v___x_2179_; 
lean_dec(v_snd_2090_);
v___x_2179_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v_quotContext_2181_; lean_object* v_currMacroScope_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_n(v_a_2180_, 31);
lean_dec_ref_known(v___x_2179_, 1);
v_quotContext_2181_ = lean_ctor_get(v___y_2074_, 10);
v_currMacroScope_2182_ = lean_ctor_get(v___y_2074_, 11);
v___x_2183_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_2184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_2185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2180_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_2187_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc_n(v_currMacroScope_2182_, 4);
lean_inc_n(v_quotContext_2181_, 4);
v___x_2189_ = l_Lean_addMacroScope(v_quotContext_2181_, v___x_2188_, v_currMacroScope_2182_);
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2180_);
lean_ctor_set(v___x_2191_, 1, v___x_2187_);
lean_ctor_set(v___x_2191_, 2, v___x_2189_);
lean_ctor_set(v___x_2191_, 3, v___x_2190_);
lean_inc_ref(v___x_2191_);
v___x_2192_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2186_, v___x_2191_);
v___x_2193_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_2194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_a_2180_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2196_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2180_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node3(v_a_2180_, v___x_2195_, v___x_2119_, v___x_2197_, v___x_2120_);
v___x_2199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_2200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2180_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_2202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_2203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2180_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_2205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_2206_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_2208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_2209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2180_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
v___x_2210_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_2211_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2180_);
lean_ctor_set(v___x_2212_, 1, v___x_2206_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2215_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2180_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2218_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2219_ = lean_box(0);
v___x_2220_ = l_Lean_addMacroScope(v_quotContext_2181_, v___x_2219_, v_currMacroScope_2182_);
v___x_2221_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_2222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2180_);
lean_ctor_set(v___x_2222_, 1, v___x_2218_);
lean_ctor_set(v___x_2222_, 2, v___x_2220_);
lean_ctor_set(v___x_2222_, 3, v___x_2221_);
v___x_2223_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2217_, v___x_2222_);
v___x_2224_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2214_, v___x_2216_, v___x_2223_);
v___x_2225_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2226_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_2227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_2228_ = l_Lean_addMacroScope(v_quotContext_2181_, v___x_2227_, v_currMacroScope_2182_);
v___x_2229_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_2230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2180_);
lean_ctor_set(v___x_2230_, 1, v___x_2226_);
lean_ctor_set(v___x_2230_, 2, v___x_2228_);
lean_ctor_set(v___x_2230_, 3, v___x_2229_);
v___x_2231_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2206_, v___x_2191_);
v___x_2232_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2225_, v___x_2230_, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2180_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_node3(v_a_2180_, v___x_2213_, v___x_2224_, v___x_2232_, v___x_2234_);
lean_inc_ref_n(v___x_2212_, 3);
v___x_2236_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2210_, v___x_2212_, v___x_2235_);
v___x_2237_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2206_, v___x_2236_);
v___x_2238_ = l_Lean_Syntax_node4(v_a_2180_, v___x_2208_, v___x_2209_, v___x_2237_, v___x_2212_, v___x_2212_);
v___x_2239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_2240_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2180_);
lean_ctor_set(v___x_2241_, 1, v___x_2239_);
v___x_2242_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2240_, v___x_2241_, v_fst_2089_);
v___x_2243_ = l_Lean_Syntax_node3(v_a_2180_, v___x_2206_, v___x_2238_, v___x_2212_, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2205_, v___x_2243_);
v___x_2245_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2204_, v___x_2244_);
v___x_2246_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2201_, v___x_2203_, v___x_2245_);
v___x_2247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_2248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_a_2180_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2251_ = l_Lean_addMacroScope(v_quotContext_2181_, v___x_2250_, v_currMacroScope_2182_);
v___x_2252_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_2253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2253_, 0, v_a_2180_);
lean_ctor_set(v___x_2253_, 1, v___x_2249_);
lean_ctor_set(v___x_2253_, 2, v___x_2251_);
lean_ctor_set(v___x_2253_, 3, v___x_2252_);
v___x_2254_ = l_Lean_Syntax_node8(v_a_2180_, v___x_2183_, v___x_2185_, v___x_2192_, v___x_2194_, v___x_2198_, v___x_2200_, v___x_2246_, v___x_2248_, v___x_2253_);
v___x_2255_ = lean_box(v___x_2124_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2255_);
lean_ctor_set(v___x_2092_, 0, v___x_2254_);
v___x_2257_ = v___x_2092_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2259_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2257_);
lean_ctor_set(v___x_2087_, 0, v___x_2122_);
v___x_2259_ = v___x_2087_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2261_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2259_);
lean_ctor_set(v___x_2083_, 0, v___x_2121_);
v___x_2261_ = v___x_2083_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
v_a_2097_ = v___x_2261_;
goto v___jp_2096_;
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_del_object(v___x_2092_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2083_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2265_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2179_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2179_);
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
v___jp_2273_:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_nat_dec_lt(v___y_2275_, v___y_2276_);
if (v___x_2277_ == 0)
{
lean_dec(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___x_2105_);
v_a_2126_ = v___x_2124_;
goto v___jp_2125_;
}
else
{
size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_usize_of_nat(v___y_2275_);
lean_dec(v___y_2275_);
v___x_2279_ = lean_usize_of_nat(v___y_2276_);
lean_dec(v___y_2276_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2105_, v___y_2274_, v___x_2278_, v___x_2279_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref(v___y_2274_);
lean_dec(v___x_2105_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; uint8_t v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = lean_unbox(v_a_2281_);
lean_dec(v_a_2281_);
v_a_2126_ = v___x_2282_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2083_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2283_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
v___jp_2291_:
{
lean_object* v___x_2294_; lean_object* v_array_2295_; lean_object* v_start_2296_; lean_object* v_stop_2297_; uint8_t v___x_2298_; 
lean_inc_ref(v_xs_2064_);
v___x_2294_ = l_Array_toSubarray___redArg(v_xs_2064_, v_lower_2292_, v_upper_2293_);
v_array_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_array_2295_);
v_start_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_start_2296_);
v_stop_2297_ = lean_ctor_get(v___x_2294_, 2);
lean_inc(v_stop_2297_);
lean_dec_ref(v___x_2294_);
v___x_2298_ = lean_nat_dec_lt(v_start_2296_, v_stop_2297_);
if (v___x_2298_ == 0)
{
lean_dec(v_stop_2297_);
lean_dec(v_start_2296_);
lean_dec_ref(v_array_2295_);
lean_dec(v___x_2105_);
v_a_2126_ = v___x_2124_;
goto v___jp_2125_;
}
else
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_array_get_size(v_array_2295_);
v___x_2300_ = lean_nat_dec_le(v_stop_2297_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v_stop_2297_);
v___y_2274_ = v_array_2295_;
v___y_2275_ = v_start_2296_;
v___y_2276_ = v___x_2299_;
goto v___jp_2273_;
}
else
{
v___y_2274_ = v_array_2295_;
v___y_2275_ = v_start_2296_;
v___y_2276_ = v_stop_2297_;
goto v___jp_2273_;
}
}
}
}
else
{
lean_object* v___x_2347_; 
lean_dec(v___x_2120_);
lean_dec(v___x_2119_);
lean_dec(v_a_2118_);
lean_dec(v_a_2116_);
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
if (v_isShared_2093_ == 0)
{
v___x_2347_ = v___x_2092_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_fst_2089_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_snd_2090_);
v___x_2347_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2347_);
lean_ctor_set(v___x_2087_, 0, v___x_2122_);
v___x_2349_ = v___x_2087_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2349_);
lean_ctor_set(v___x_2083_, 0, v___x_2121_);
v___x_2351_ = v___x_2083_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
v_a_2097_ = v___x_2351_;
goto v___jp_2096_;
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_a_2116_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2355_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2117_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2117_);
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
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2363_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2115_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2115_);
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
lean_dec(v_a_2110_);
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2371_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2113_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2113_);
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
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_a_2108_);
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2379_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2109_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2109_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2387_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2107_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2107_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v___x_2395_; 
lean_dec(v___x_2105_);
lean_dec(v___x_2102_);
v___x_2395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc_n(v_a_2396_, 2);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2398_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_a_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_node1(v_a_2396_, v___x_2397_, v___x_2399_);
v___x_2401_ = lean_array_push(v_fst_2081_, v___x_2400_);
if (v_isShared_2093_ == 0)
{
v___x_2403_ = v___x_2092_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_fst_2089_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_snd_2090_);
v___x_2403_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2403_);
v___x_2405_ = v___x_2087_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_fst_2085_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2405_);
lean_ctor_set(v___x_2083_, 0, v___x_2401_);
v___x_2407_ = v___x_2083_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
v_a_2097_ = v___x_2407_;
goto v___jp_2096_;
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_fst_2085_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2081_);
lean_dec(v_a_2068_);
lean_dec(v_auxFunName_2067_);
lean_dec_ref(v_xs_2064_);
v_a_2411_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2395_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2395_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
v___jp_2096_:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_nat_add(v_a_2068_, v___x_2095_);
lean_dec(v_a_2068_);
v_a_2068_ = v___x_2098_;
v_b_2069_ = v_a_2097_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object* v_upperBound_2424_, lean_object* v_indVal_2425_, lean_object* v___x_2426_, lean_object* v_xs_2427_, lean_object* v_a_2428_, lean_object* v___x_2429_, lean_object* v_auxFunName_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_2424_, v_indVal_2425_, v___x_2426_, v_xs_2427_, v_a_2428_, v___x_2429_, v_auxFunName_2430_, v_a_2431_, v_b_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___x_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v___x_2426_);
lean_dec_ref(v_indVal_2425_);
lean_dec(v_upperBound_2424_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(uint8_t v_rhs__empty_2468_, lean_object* v_numFields_2469_, lean_object* v_indVal_2470_, lean_object* v_name_2471_, lean_object* v_auxFunName_2472_, lean_object* v___f_2473_, lean_object* v_xs_2474_, lean_object* v_type_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Core_betaReduce(v_type_2475_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v_ref_2485_; lean_object* v_quotContext_2486_; lean_object* v_currMacroScope_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_ref_2485_ = lean_ctor_get(v___y_2480_, 5);
v_quotContext_2486_ = lean_ctor_get(v___y_2480_, 10);
v_currMacroScope_2487_ = lean_ctor_get(v___y_2480_, 11);
v___x_2488_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_2489_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_2492_ = 0;
v___x_2493_ = l_Lean_SourceInfo_fromRef(v_ref_2485_, v___x_2492_);
lean_inc(v_currMacroScope_2487_);
lean_inc(v_quotContext_2486_);
v___x_2494_ = l_Lean_addMacroScope(v_quotContext_2486_, v___x_2489_, v_currMacroScope_2487_);
v___x_2495_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_2496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2493_);
lean_ctor_set(v___x_2496_, 1, v___x_2488_);
lean_ctor_set(v___x_2496_, 2, v___x_2494_);
lean_ctor_set(v___x_2496_, 3, v___x_2495_);
v___x_2497_ = lean_box(v_rhs__empty_2468_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2491_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2491_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_numFields_2469_, v_indVal_2470_, v_numFields_2469_, v_xs_2474_, v_a_2484_, v_name_2471_, v_auxFunName_2472_, v___x_2490_, v___x_2500_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v_a_2484_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v_snd_2503_; lean_object* v_snd_2504_; lean_object* v_fst_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2603_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v_snd_2503_ = lean_ctor_get(v_a_2502_, 1);
lean_inc(v_snd_2503_);
v_snd_2504_ = lean_ctor_get(v_snd_2503_, 1);
lean_inc(v_snd_2504_);
v_fst_2505_ = lean_ctor_get(v_a_2502_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_a_2502_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v_a_2502_, 1);
lean_dec(v_unused_2604_);
v___x_2507_ = v_a_2502_;
v_isShared_2508_ = v_isSharedCheck_2603_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_fst_2505_);
lean_dec(v_a_2502_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2603_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v_fst_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2601_; 
v_fst_2509_ = lean_ctor_get(v_snd_2503_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_snd_2503_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v_snd_2503_, 1);
lean_dec(v_unused_2602_);
v___x_2511_ = v_snd_2503_;
v_isShared_2512_ = v_isSharedCheck_2601_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_fst_2509_);
lean_dec(v_snd_2503_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2601_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_fst_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2599_; 
v_fst_2513_ = lean_ctor_get(v_snd_2504_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_snd_2504_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v_snd_2504_, 1);
lean_dec(v_unused_2600_);
v___x_2515_ = v_snd_2504_;
v_isShared_2516_ = v_isSharedCheck_2599_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_fst_2513_);
lean_dec(v_snd_2504_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2599_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_ctorArgs1_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_array_get_size(v_fst_2505_);
v___x_2569_ = lean_nat_dec_eq(v___x_2568_, v___x_2490_);
if (v___x_2569_ == 0)
{
v_ctorArgs1_2518_ = v_fst_2505_;
v___y_2519_ = v___y_2476_;
v___y_2520_ = v___y_2477_;
v___y_2521_ = v___y_2478_;
v___y_2522_ = v___y_2479_;
v___y_2523_ = v___y_2480_;
v___y_2524_ = v___y_2481_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2570_; 
lean_inc_ref(v___f_2473_);
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
v___x_2570_ = lean_apply_7(v___f_2473_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, lean_box(0));
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_n(v_a_2571_, 7);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5));
v___x_2573_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2571_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2577_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2578_ = lean_box(0);
lean_inc(v_currMacroScope_2487_);
lean_inc(v_quotContext_2486_);
v___x_2579_ = l_Lean_addMacroScope(v_quotContext_2486_, v___x_2578_, v_currMacroScope_2487_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2571_);
lean_ctor_set(v___x_2581_, 1, v___x_2577_);
lean_ctor_set(v___x_2581_, 2, v___x_2579_);
lean_ctor_set(v___x_2581_, 3, v___x_2580_);
v___x_2582_ = l_Lean_Syntax_node1(v_a_2571_, v___x_2576_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node2(v_a_2571_, v___x_2573_, v___x_2575_, v___x_2582_);
v___x_2584_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2585_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2571_);
lean_ctor_set(v___x_2586_, 1, v___x_2584_);
lean_ctor_set(v___x_2586_, 2, v___x_2585_);
v___x_2587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_a_2571_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_Syntax_node3(v_a_2571_, v___x_2572_, v___x_2583_, v___x_2586_, v___x_2588_);
v___x_2590_ = lean_array_push(v_fst_2505_, v___x_2589_);
v_ctorArgs1_2518_ = v___x_2590_;
v___y_2519_ = v___y_2476_;
v___y_2520_ = v___y_2477_;
v___y_2521_ = v___y_2478_;
v___y_2522_ = v___y_2479_;
v___y_2523_ = v___y_2480_;
v___y_2524_ = v___y_2481_;
goto v___jp_2517_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_del_object(v___x_2515_);
lean_dec(v_fst_2513_);
lean_del_object(v___x_2511_);
lean_dec(v_fst_2509_);
lean_del_object(v___x_2507_);
lean_dec(v_fst_2505_);
lean_dec_ref(v___f_2473_);
v_a_2591_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2570_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2570_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
v___jp_2517_:
{
lean_object* v___x_2525_; 
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
v___x_2525_ = lean_apply_7(v___f_2473_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, lean_box(0));
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2559_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2559_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2559_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2530_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
v___x_2531_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_2526_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 2);
lean_ctor_set(v___x_2515_, 1, v___x_2531_);
lean_ctor_set(v___x_2515_, 0, v_a_2526_);
v___x_2533_ = v___x_2515_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2526_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0));
v___x_2535_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1));
lean_inc(v_a_2526_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 2);
lean_ctor_set(v___x_2511_, 1, v___x_2534_);
lean_ctor_set(v___x_2511_, 0, v_a_2526_);
v___x_2537_ = v___x_2511_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2526_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2534_);
v___x_2537_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3));
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2540_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2541_ = l_Array_reverse___redArg(v_ctorArgs1_2518_);
v___x_2542_ = l_Array_append___redArg(v___x_2540_, v___x_2541_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = l_Array_reverse___redArg(v_fst_2509_);
v___x_2544_ = l_Array_append___redArg(v___x_2542_, v___x_2543_);
lean_dec_ref(v___x_2543_);
lean_inc_n(v_a_2526_, 3);
v___x_2545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2545_, 0, v_a_2526_);
lean_ctor_set(v___x_2545_, 1, v___x_2539_);
lean_ctor_set(v___x_2545_, 2, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2526_);
lean_ctor_set(v___x_2546_, 1, v___x_2539_);
lean_ctor_set(v___x_2546_, 2, v___x_2540_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 2);
lean_ctor_set(v___x_2507_, 1, v___x_2547_);
lean_ctor_set(v___x_2507_, 0, v_a_2526_);
v___x_2549_ = v___x_2507_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2526_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_inc_n(v_a_2526_, 2);
v___x_2550_ = l_Lean_Syntax_node4(v_a_2526_, v___x_2538_, v___x_2545_, v___x_2546_, v___x_2549_, v_fst_2513_);
v___x_2551_ = l_Lean_Syntax_node2(v_a_2526_, v___x_2535_, v___x_2537_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node2(v_a_2526_, v___x_2530_, v___x_2533_, v___x_2551_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2552_);
v___x_2554_ = v___x_2528_;
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
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref(v_ctorArgs1_2518_);
lean_del_object(v___x_2515_);
lean_dec(v_fst_2513_);
lean_del_object(v___x_2511_);
lean_dec(v_fst_2509_);
lean_del_object(v___x_2507_);
v_a_2560_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2525_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2525_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
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
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___f_2473_);
v_a_2605_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2501_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2501_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_xs_2474_);
lean_dec_ref(v___f_2473_);
lean_dec(v_auxFunName_2472_);
v_a_2613_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2483_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2483_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object* v_rhs__empty_2621_, lean_object* v_numFields_2622_, lean_object* v_indVal_2623_, lean_object* v_name_2624_, lean_object* v_auxFunName_2625_, lean_object* v___f_2626_, lean_object* v_xs_2627_, lean_object* v_type_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v_rhs__empty_boxed_2636_; lean_object* v_res_2637_; 
v_rhs__empty_boxed_2636_ = lean_unbox(v_rhs__empty_2621_);
v_res_2637_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(v_rhs__empty_boxed_2636_, v_numFields_2622_, v_indVal_2623_, v_name_2624_, v_auxFunName_2625_, v___f_2626_, v_xs_2627_, v_type_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v_name_2624_);
lean_dec_ref(v_indVal_2623_);
lean_dec(v_numFields_2622_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object* v___x_2638_, lean_object* v_ctors_2639_, uint8_t v_rhs__empty_2640_, lean_object* v_indVal_2641_, lean_object* v_name_2642_, lean_object* v_auxFunName_2643_, lean_object* v___f_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = l_List_get_x21Internal___redArg(v___x_2638_, v_ctors_2639_, v_x_2645_);
v___x_2654_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v___x_2653_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_toConstantVal_2656_; lean_object* v_numFields_2657_; lean_object* v_type_2658_; lean_object* v___x_2659_; lean_object* v___f_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v_toConstantVal_2656_ = lean_ctor_get(v_a_2655_, 0);
lean_inc_ref(v_toConstantVal_2656_);
v_numFields_2657_ = lean_ctor_get(v_a_2655_, 4);
lean_inc(v_numFields_2657_);
lean_dec(v_a_2655_);
v_type_2658_ = lean_ctor_get(v_toConstantVal_2656_, 2);
lean_inc_ref(v_type_2658_);
lean_dec_ref(v_toConstantVal_2656_);
v___x_2659_ = lean_box(v_rhs__empty_2640_);
v___f_2660_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2660_, 0, v___x_2659_);
lean_closure_set(v___f_2660_, 1, v_numFields_2657_);
lean_closure_set(v___f_2660_, 2, v_indVal_2641_);
lean_closure_set(v___f_2660_, 3, v_name_2642_);
lean_closure_set(v___f_2660_, 4, v_auxFunName_2643_);
lean_closure_set(v___f_2660_, 5, v___f_2644_);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_2658_, v___f_2660_, v___x_2661_, v___x_2661_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
return v___x_2662_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v___f_2644_);
lean_dec(v_auxFunName_2643_);
lean_dec(v_name_2642_);
lean_dec_ref(v_indVal_2641_);
v_a_2663_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2654_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object* v___x_2671_, lean_object* v_ctors_2672_, lean_object* v_rhs__empty_2673_, lean_object* v_indVal_2674_, lean_object* v_name_2675_, lean_object* v_auxFunName_2676_, lean_object* v___f_2677_, lean_object* v_x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v_rhs__empty_boxed_2686_; lean_object* v_res_2687_; 
v_rhs__empty_boxed_2686_ = lean_unbox(v_rhs__empty_2673_);
v_res_2687_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(v___x_2671_, v_ctors_2672_, v_rhs__empty_boxed_2686_, v_indVal_2674_, v_name_2675_, v_auxFunName_2676_, v___f_2677_, v_x_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v_ctors_2672_);
lean_dec(v___x_2671_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object* v_f_2688_, lean_object* v_n_2689_, lean_object* v_x_2690_, lean_object* v_i_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_lt(v_i_2691_, v_n_2689_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_dec(v_i_2691_);
lean_dec_ref(v_f_2688_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_x_2690_);
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; 
lean_inc_ref(v_f_2688_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v_i_2691_);
v___x_2701_ = lean_apply_8(v_f_2688_, v_i_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_array_push(v_x_2690_, v_a_2702_);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_i_2691_, v___x_2704_);
lean_dec(v_i_2691_);
v_x_2690_ = v___x_2703_;
v_i_2691_ = v___x_2705_;
goto _start;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_i_2691_);
lean_dec_ref(v_x_2690_);
lean_dec_ref(v_f_2688_);
v_a_2707_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2701_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2701_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object* v_f_2715_, lean_object* v_n_2716_, lean_object* v_x_2717_, lean_object* v_i_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2715_, v_n_2716_, v_x_2717_, v_i_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v_n_2716_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object* v_n_2727_, lean_object* v_f_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_mk_empty_array_with_capacity(v_n_2727_);
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2728_, v_n_2727_, v___x_2736_, v___x_2737_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object* v_n_2739_, lean_object* v_f_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_2739_, v_f_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v_n_2739_);
return v_res_2748_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2));
v___x_2753_ = lean_unsigned_to_nat(2u);
v___x_2754_ = lean_unsigned_to_nat(113u);
v___x_2755_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1));
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0));
v___x_2757_ = l_mkPanicMessageWithDecl(v___x_2756_, v___x_2755_, v___x_2754_, v___x_2753_, v___x_2752_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8));
v___x_2769_ = l_String_toRawSubstring_x27(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20));
v___x_2795_ = l_String_toRawSubstring_x27(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27));
v___x_2810_ = l_String_toRawSubstring_x27(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33));
v___x_2824_ = l_String_toRawSubstring_x27(v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object* v_header_2833_, lean_object* v_indVal_2834_, lean_object* v_auxFunName_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_targetNames_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_3036_; 
v_targetNames_2843_ = lean_ctor_get(v_header_2833_, 2);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_header_2833_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; lean_object* v_unused_3038_; lean_object* v_unused_3039_; 
v_unused_3037_ = lean_ctor_get(v_header_2833_, 3);
lean_dec(v_unused_3037_);
v_unused_3038_ = lean_ctor_get(v_header_2833_, 1);
lean_dec(v_unused_3038_);
v_unused_3039_ = lean_ctor_get(v_header_2833_, 0);
lean_dec(v_unused_3039_);
v___x_2845_ = v_header_2833_;
v_isShared_2846_ = v_isSharedCheck_3036_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_targetNames_2843_);
lean_dec(v_header_2833_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_3036_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v_rhs__empty_2849_; 
v___x_2847_ = lean_array_get_size(v_targetNames_2843_);
v___x_2848_ = lean_unsigned_to_nat(2u);
v_rhs__empty_2849_ = lean_nat_dec_eq(v___x_2847_, v___x_2848_);
if (v_rhs__empty_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_del_object(v___x_2845_);
lean_dec_ref(v_targetNames_2843_);
lean_dec(v_auxFunName_2835_);
lean_dec_ref(v_indVal_2834_);
v___x_2850_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3);
v___x_2851_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v___x_2850_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
return v___x_2851_;
}
else
{
lean_object* v_toConstantVal_2852_; lean_object* v_ctors_2853_; lean_object* v_name_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3033_; 
v_toConstantVal_2852_ = lean_ctor_get(v_indVal_2834_, 0);
lean_inc_ref(v_toConstantVal_2852_);
v_ctors_2853_ = lean_ctor_get(v_indVal_2834_, 4);
v_name_2854_ = lean_ctor_get(v_toConstantVal_2852_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_toConstantVal_2852_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; lean_object* v_unused_3035_; 
v_unused_3034_ = lean_ctor_get(v_toConstantVal_2852_, 2);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v_toConstantVal_2852_, 1);
lean_dec(v_unused_3035_);
v___x_2856_ = v_toConstantVal_2852_;
v_isShared_2857_ = v_isSharedCheck_3033_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_name_2854_);
lean_dec(v_toConstantVal_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3033_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_ctorIdxName_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_inc_n(v_name_2854_, 2);
v_ctorIdxName_2858_ = l_Lean_mkCtorIdxName(v_name_2854_);
v___x_2859_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5));
v___x_2860_ = l_Lean_Name_append(v_name_2854_, v___x_2859_);
v___x_2861_ = l_Lean_Core_mkFreshUserName(v___x_2860_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc_n(v_a_2862_, 2);
lean_dec_ref_known(v___x_2861_, 1);
lean_inc(v_name_2854_);
v___x_2863_ = l_Lean_mkCasesOnSameCtor(v_a_2862_, v_name_2854_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec_ref_known(v___x_2863_, 1);
v___f_2864_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_box(v_rhs__empty_2849_);
lean_inc_ref(v_indVal_2834_);
lean_inc(v_ctors_2853_);
v___f_2867_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2867_, 0, v___x_2865_);
lean_closure_set(v___f_2867_, 1, v_ctors_2853_);
lean_closure_set(v___f_2867_, 2, v___x_2866_);
lean_closure_set(v___f_2867_, 3, v_indVal_2834_);
lean_closure_set(v___f_2867_, 4, v_name_2854_);
lean_closure_set(v___f_2867_, 5, v_auxFunName_2835_);
lean_closure_set(v___f_2867_, 6, v___f_2864_);
v___x_2868_ = l_Lean_InductiveVal_numCtors(v_indVal_2834_);
lean_dec_ref(v_indVal_2834_);
v___x_2869_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v___x_2868_, v___f_2867_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_3008_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_3008_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_3008_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_x1_2877_; lean_object* v___x_2878_; lean_object* v_x2_2879_; uint8_t v___x_2880_; 
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_array_get_borrowed(v___x_2865_, v_targetNames_2843_, v___x_2875_);
lean_inc(v___x_2876_);
v_x1_2877_ = l_Lean_mkIdent(v___x_2876_);
v___x_2878_ = lean_array_get(v___x_2865_, v_targetNames_2843_, v___x_2874_);
lean_dec_ref(v_targetNames_2843_);
v_x2_2879_ = l_Lean_mkIdent(v___x_2878_);
v___x_2880_ = lean_nat_dec_eq(v___x_2868_, v___x_2874_);
lean_dec(v___x_2868_);
if (v___x_2880_ == 0)
{
lean_object* v_ref_2881_; lean_object* v_quotContext_2882_; lean_object* v_currMacroScope_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v_ref_2881_ = lean_ctor_get(v_a_2840_, 5);
v_quotContext_2882_ = lean_ctor_get(v_a_2840_, 10);
v_currMacroScope_2883_ = lean_ctor_get(v_a_2840_, 11);
v___x_2884_ = l_Lean_SourceInfo_fromRef(v_ref_2881_, v___x_2880_);
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_2884_, 2);
v___x_2887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2884_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
v___x_2888_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2889_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 1);
lean_ctor_set(v___x_2856_, 2, v___x_2889_);
lean_ctor_set(v___x_2856_, 1, v___x_2888_);
lean_ctor_set(v___x_2856_, 0, v___x_2884_);
v___x_2891_ = v___x_2856_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7));
v___x_2893_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2894_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9);
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12));
lean_inc(v_currMacroScope_2883_);
lean_inc(v_quotContext_2882_);
v___x_2896_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2895_, v_currMacroScope_2883_);
v___x_2897_ = lean_box(0);
v___x_2898_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16));
lean_inc(v___x_2884_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 3);
lean_ctor_set(v___x_2845_, 3, v___x_2898_);
lean_ctor_set(v___x_2845_, 2, v___x_2896_);
lean_ctor_set(v___x_2845_, 1, v___x_2894_);
lean_ctor_set(v___x_2845_, 0, v___x_2884_);
v___x_2900_ = v___x_2845_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2901_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2902_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v___x_2884_, 41);
v___x_2904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2884_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2906_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
lean_inc_n(v_currMacroScope_2883_, 5);
lean_inc_n(v_quotContext_2882_, 5);
v___x_2907_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2865_, v_currMacroScope_2883_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2884_);
lean_ctor_set(v___x_2909_, 1, v___x_2906_);
lean_ctor_set(v___x_2909_, 2, v___x_2907_);
lean_ctor_set(v___x_2909_, 3, v___x_2908_);
v___x_2910_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2905_, v___x_2909_);
v___x_2911_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2902_, v___x_2904_, v___x_2910_);
v___x_2912_ = l_Lean_mkCIdent(v_ctorIdxName_2858_);
lean_inc(v_x1_2877_);
v___x_2913_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v_x1_2877_);
lean_inc(v___x_2912_);
v___x_2914_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2912_, v___x_2913_);
v___x_2915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2884_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
lean_inc_ref(v___x_2916_);
lean_inc(v___x_2911_);
v___x_2917_ = l_Lean_Syntax_node3(v___x_2884_, v___x_2901_, v___x_2911_, v___x_2914_, v___x_2916_);
lean_inc(v_x2_2879_);
v___x_2918_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v_x2_2879_);
v___x_2919_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2912_, v___x_2918_);
v___x_2920_ = l_Lean_Syntax_node3(v___x_2884_, v___x_2901_, v___x_2911_, v___x_2919_, v___x_2916_);
v___x_2921_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2888_, v___x_2917_, v___x_2920_);
v___x_2922_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2900_, v___x_2921_);
lean_inc_ref_n(v___x_2891_, 2);
v___x_2923_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2892_, v___x_2891_, v___x_2922_);
v___x_2924_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2923_);
v___x_2925_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_2926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2884_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_2928_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_2929_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
v___x_2930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2884_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18));
v___x_2932_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19));
v___x_2933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2884_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21);
v___x_2935_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22));
v___x_2936_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2935_, v_currMacroScope_2883_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26));
v___x_2938_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2884_);
lean_ctor_set(v___x_2938_, 1, v___x_2934_);
lean_ctor_set(v___x_2938_, 2, v___x_2936_);
lean_ctor_set(v___x_2938_, 3, v___x_2937_);
lean_inc_ref(v___x_2933_);
v___x_2939_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2931_, v___x_2933_, v___x_2938_);
v___x_2940_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2941_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
v___x_2942_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2941_, v_currMacroScope_2883_);
v___x_2943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2884_);
lean_ctor_set(v___x_2943_, 1, v___x_2940_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
lean_ctor_set(v___x_2943_, 3, v___x_2897_);
lean_inc_ref(v___x_2943_);
v___x_2944_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2943_);
v___x_2945_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2939_, v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2945_);
v___x_2947_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2884_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = l_Lean_mkCIdent(v_a_2862_);
v___x_2951_ = l_Array_mkArray3___redArg(v_x1_2877_, v_x2_2879_, v___x_2943_);
v___x_2952_ = l_Array_append___redArg(v___x_2951_, v_a_2870_);
lean_dec(v_a_2870_);
v___x_2953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2884_);
lean_ctor_set(v___x_2953_, 1, v___x_2888_);
lean_ctor_set(v___x_2953_, 2, v___x_2952_);
v___x_2954_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2950_, v___x_2953_);
lean_inc_ref(v___x_2949_);
lean_inc_ref(v___x_2930_);
v___x_2955_ = l_Lean_Syntax_node4(v___x_2884_, v___x_2928_, v___x_2930_, v___x_2947_, v___x_2949_, v___x_2954_);
v___x_2956_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28);
v___x_2957_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29));
v___x_2958_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2957_, v_currMacroScope_2883_);
v___x_2959_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32));
v___x_2960_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2884_);
lean_ctor_set(v___x_2960_, 1, v___x_2956_);
lean_ctor_set(v___x_2960_, 2, v___x_2958_);
lean_ctor_set(v___x_2960_, 3, v___x_2959_);
v___x_2961_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2931_, v___x_2933_, v___x_2960_);
v___x_2962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2884_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2962_, v___x_2964_);
v___x_2966_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2965_);
v___x_2967_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2893_, v___x_2961_, v___x_2966_);
v___x_2968_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2967_);
v___x_2969_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2888_, v___x_2968_);
v___x_2970_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2972_ = l_Lean_addMacroScope(v_quotContext_2882_, v___x_2971_, v_currMacroScope_2883_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_2974_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2884_);
lean_ctor_set(v___x_2974_, 1, v___x_2970_);
lean_ctor_set(v___x_2974_, 2, v___x_2972_);
lean_ctor_set(v___x_2974_, 3, v___x_2973_);
v___x_2975_ = l_Lean_Syntax_node4(v___x_2884_, v___x_2928_, v___x_2930_, v___x_2969_, v___x_2949_, v___x_2974_);
v___x_2976_ = l_Lean_Syntax_node2(v___x_2884_, v___x_2888_, v___x_2955_, v___x_2975_);
v___x_2977_ = l_Lean_Syntax_node1(v___x_2884_, v___x_2927_, v___x_2976_);
v___x_2978_ = l_Lean_Syntax_node6(v___x_2884_, v___x_2886_, v___x_2887_, v___x_2891_, v___x_2891_, v___x_2924_, v___x_2926_, v___x_2977_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2978_);
v___x_2980_ = v___x_2872_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_ref_2984_; lean_object* v_quotContext_2985_; lean_object* v_currMacroScope_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_dec(v_ctorIdxName_2858_);
v_ref_2984_ = lean_ctor_get(v_a_2840_, 5);
v_quotContext_2985_ = lean_ctor_get(v_a_2840_, 10);
v_currMacroScope_2986_ = lean_ctor_get(v_a_2840_, 11);
v___x_2987_ = 0;
v___x_2988_ = l_Lean_SourceInfo_fromRef(v_ref_2984_, v___x_2987_);
v___x_2989_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2990_ = l_Lean_mkCIdent(v_a_2862_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2992_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34);
v___x_2993_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35));
lean_inc(v_currMacroScope_2986_);
lean_inc(v_quotContext_2985_);
v___x_2994_ = l_Lean_addMacroScope(v_quotContext_2985_, v___x_2993_, v_currMacroScope_2986_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37));
lean_inc(v___x_2988_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 3);
lean_ctor_set(v___x_2845_, 3, v___x_2995_);
lean_ctor_set(v___x_2845_, 2, v___x_2994_);
lean_ctor_set(v___x_2845_, 1, v___x_2992_);
lean_ctor_set(v___x_2845_, 0, v___x_2988_);
v___x_2997_ = v___x_2845_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2998_ = l_Array_mkArray3___redArg(v_x1_2877_, v_x2_2879_, v___x_2997_);
v___x_2999_ = l_Array_append___redArg(v___x_2998_, v_a_2870_);
lean_dec(v_a_2870_);
lean_inc(v___x_2988_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 1);
lean_ctor_set(v___x_2856_, 2, v___x_2999_);
lean_ctor_set(v___x_2856_, 1, v___x_2991_);
lean_ctor_set(v___x_2856_, 0, v___x_2988_);
v___x_3001_ = v___x_2856_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = l_Lean_Syntax_node2(v___x_2988_, v___x_2989_, v___x_2990_, v___x_3001_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_3002_);
v___x_3004_ = v___x_2872_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
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
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___x_2868_);
lean_dec(v_a_2862_);
lean_dec(v_ctorIdxName_2858_);
lean_del_object(v___x_2856_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_targetNames_2843_);
v_a_3009_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2869_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2869_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v_a_2862_);
lean_dec(v_ctorIdxName_2858_);
lean_del_object(v___x_2856_);
lean_dec(v_name_2854_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_targetNames_2843_);
lean_dec(v_auxFunName_2835_);
lean_dec_ref(v_indVal_2834_);
v_a_3017_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2863_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2863_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_ctorIdxName_2858_);
lean_del_object(v___x_2856_);
lean_dec(v_name_2854_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_targetNames_2843_);
lean_dec(v_auxFunName_2835_);
lean_dec_ref(v_indVal_2834_);
v_a_3025_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2861_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2861_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object* v_header_3040_, lean_object* v_indVal_3041_, lean_object* v_auxFunName_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3040_, v_indVal_3041_, v_auxFunName_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object* v___x_3051_, lean_object* v_as_3052_, size_t v_i_3053_, size_t v_stop_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_3051_, v_as_3052_, v_i_3053_, v_stop_3054_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object* v___x_3063_, lean_object* v_as_3064_, lean_object* v_i_3065_, lean_object* v_stop_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
size_t v_i_boxed_3074_; size_t v_stop_boxed_3075_; lean_object* v_res_3076_; 
v_i_boxed_3074_ = lean_unbox_usize(v_i_3065_);
lean_dec(v_i_3065_);
v_stop_boxed_3075_ = lean_unbox_usize(v_stop_3066_);
lean_dec(v_stop_3066_);
v_res_3076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(v___x_3063_, v_as_3064_, v_i_boxed_3074_, v_stop_boxed_3075_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_as_3064_);
lean_dec(v___x_3063_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object* v_upperBound_3077_, lean_object* v_indVal_3078_, lean_object* v___x_3079_, lean_object* v_xs_3080_, lean_object* v_a_3081_, lean_object* v___x_3082_, lean_object* v_auxFunName_3083_, lean_object* v_inst_3084_, lean_object* v_R_3085_, lean_object* v_a_3086_, lean_object* v_b_3087_, lean_object* v_c_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_3077_, v_indVal_3078_, v___x_3079_, v_xs_3080_, v_a_3081_, v___x_3082_, v_auxFunName_3083_, v_a_3086_, v_b_3087_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_3097_ = _args[0];
lean_object* v_indVal_3098_ = _args[1];
lean_object* v___x_3099_ = _args[2];
lean_object* v_xs_3100_ = _args[3];
lean_object* v_a_3101_ = _args[4];
lean_object* v___x_3102_ = _args[5];
lean_object* v_auxFunName_3103_ = _args[6];
lean_object* v_inst_3104_ = _args[7];
lean_object* v_R_3105_ = _args[8];
lean_object* v_a_3106_ = _args[9];
lean_object* v_b_3107_ = _args[10];
lean_object* v_c_3108_ = _args[11];
lean_object* v___y_3109_ = _args[12];
lean_object* v___y_3110_ = _args[13];
lean_object* v___y_3111_ = _args[14];
lean_object* v___y_3112_ = _args[15];
lean_object* v___y_3113_ = _args[16];
lean_object* v___y_3114_ = _args[17];
lean_object* v___y_3115_ = _args[18];
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(v_upperBound_3097_, v_indVal_3098_, v___x_3099_, v_xs_3100_, v_a_3101_, v___x_3102_, v_auxFunName_3103_, v_inst_3104_, v_R_3105_, v_a_3106_, v_b_3107_, v_c_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___x_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v___x_3099_);
lean_dec_ref(v_indVal_3098_);
lean_dec(v_upperBound_3097_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object* v_00_u03b1_3117_, lean_object* v_n_3118_, lean_object* v_f_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_3118_, v_f_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_n_3129_, lean_object* v_f_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(v_00_u03b1_3128_, v_n_3129_, v_f_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v_n_3129_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object* v_00_u03b1_3139_, lean_object* v_f_3140_, lean_object* v_n_3141_, lean_object* v_x_3142_, lean_object* v_i_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_3140_, v_n_3141_, v_x_3142_, v_i_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3152_, lean_object* v_f_3153_, lean_object* v_n_3154_, lean_object* v_x_3155_, lean_object* v_i_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(v_00_u03b1_3152_, v_f_3153_, v_n_3154_, v_x_3155_, v_i_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v_n_3154_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object* v_opts_3165_, lean_object* v_opt_3166_){
_start:
{
lean_object* v_name_3167_; lean_object* v_defValue_3168_; lean_object* v_map_3169_; lean_object* v___x_3170_; 
v_name_3167_ = lean_ctor_get(v_opt_3166_, 0);
v_defValue_3168_ = lean_ctor_get(v_opt_3166_, 1);
v_map_3169_ = lean_ctor_get(v_opts_3165_, 0);
v___x_3170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3169_, v_name_3167_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_inc(v_defValue_3168_);
return v_defValue_3168_;
}
else
{
lean_object* v_val_3171_; 
v_val_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v___x_3170_, 1);
if (lean_obj_tag(v_val_3171_) == 3)
{
lean_object* v_v_3172_; 
v_v_3172_ = lean_ctor_get(v_val_3171_, 0);
lean_inc(v_v_3172_);
lean_dec_ref_known(v_val_3171_, 1);
return v_v_3172_;
}
else
{
lean_dec(v_val_3171_);
lean_inc(v_defValue_3168_);
return v_defValue_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object* v_opts_3173_, lean_object* v_opt_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_opts_3173_, v_opt_3174_);
lean_dec_ref(v_opt_3174_);
lean_dec_ref(v_opts_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object* v_header_3176_, lean_object* v_indVal_3177_, lean_object* v_auxFunName_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_options_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v_options_3186_ = lean_ctor_get(v_a_3183_, 2);
v___x_3187_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
v___x_3188_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_options_3186_, v___x_3187_);
v___x_3189_ = l_Lean_InductiveVal_numCtors(v_indVal_3177_);
v___x_3190_ = lean_nat_dec_le(v___x_3188_, v___x_3189_);
lean_dec(v___x_3189_);
lean_dec(v___x_3188_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_3176_, v_indVal_3177_, v_auxFunName_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; 
v___x_3192_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3176_, v_indVal_3177_, v_auxFunName_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object* v_header_3193_, lean_object* v_indVal_3194_, lean_object* v_auxFunName_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_header_3193_, v_indVal_3194_, v_auxFunName_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
return v_res_3203_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4));
v___x_3243_ = l_String_toRawSubstring_x27(v___x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object* v_ctx_3280_, lean_object* v_i_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_typeInfos_3289_; lean_object* v_auxFunNames_3290_; uint8_t v_usePartial_3291_; lean_object* v___x_3292_; lean_object* v_indVal_3293_; lean_object* v___x_3294_; 
v_typeInfos_3289_ = lean_ctor_get(v_ctx_3280_, 1);
v_auxFunNames_3290_ = lean_ctor_get(v_ctx_3280_, 2);
v_usePartial_3291_ = lean_ctor_get_uint8(v_ctx_3280_, sizeof(void*)*3);
v___x_3292_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_3293_ = lean_array_get_borrowed(v___x_3292_, v_typeInfos_3289_, v_i_3281_);
lean_inc(v_indVal_3293_);
v___x_3294_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_3293_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3429_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3429_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3429_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v_auxFunName_3300_; lean_object* v_body_3302_; lean_object* v___y_3303_; lean_object* v___x_3412_; 
v___x_3299_ = lean_box(0);
v_auxFunName_3300_ = lean_array_get_borrowed(v___x_3299_, v_auxFunNames_3290_, v_i_3281_);
lean_inc(v_auxFunName_3300_);
lean_inc(v_indVal_3293_);
lean_inc(v_a_3295_);
v___x_3412_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_a_3295_, v_indVal_3293_, v_auxFunName_3300_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3412_) == 0)
{
if (v_usePartial_3291_ == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v_body_3302_ = v_a_3413_;
v___y_3303_ = v_a_3286_;
goto v___jp_3301_;
}
else
{
lean_object* v_a_3414_; lean_object* v_argNames_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_a_3414_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3412_, 1);
v_argNames_3415_ = lean_ctor_get(v_a_3295_, 1);
v___x_3416_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
lean_inc_ref(v_argNames_3415_);
v___x_3417_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_3280_, v___x_3416_, v_argNames_3415_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = l_Lean_Elab_Deriving_mkLet(v_a_3418_, v_a_3414_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
lean_dec(v_a_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v_body_3302_ = v_a_3420_;
v___y_3303_ = v_a_3286_;
goto v___jp_3301_;
}
else
{
lean_del_object(v___x_3297_);
lean_dec(v_a_3295_);
return v___x_3419_;
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_a_3414_);
lean_del_object(v___x_3297_);
lean_dec(v_a_3295_);
v_a_3421_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3417_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
else
{
lean_del_object(v___x_3297_);
lean_dec(v_a_3295_);
return v___x_3412_;
}
v___jp_3301_:
{
if (v_usePartial_3291_ == 0)
{
lean_object* v_binders_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3351_; 
v_binders_3304_ = lean_ctor_get(v_a_3295_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_a_3295_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3352_ = lean_ctor_get(v_a_3295_, 3);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_a_3295_, 2);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_a_3295_, 1);
lean_dec(v_unused_3354_);
v___x_3306_ = v_a_3295_;
v_isShared_3307_ = v_isSharedCheck_3351_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_binders_3304_);
lean_dec(v_a_3295_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3351_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_ref_3308_; lean_object* v_quotContext_3309_; lean_object* v_currMacroScope_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v_ref_3308_ = lean_ctor_get(v___y_3303_, 5);
v_quotContext_3309_ = lean_ctor_get(v___y_3303_, 10);
v_currMacroScope_3310_ = lean_ctor_get(v___y_3303_, 11);
v___x_3311_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v_usePartial_3291_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3315_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3311_, 7);
v___x_3316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3311_);
lean_ctor_set(v___x_3316_, 1, v___x_3314_);
lean_ctor_set(v___x_3316_, 2, v___x_3315_);
lean_inc_ref_n(v___x_3316_, 8);
v___x_3317_ = l_Lean_Syntax_node7(v___x_3311_, v___x_3313_, v___x_3316_, v___x_3316_, v___x_3316_, v___x_3316_, v___x_3316_, v___x_3316_, v___x_3316_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3311_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3300_);
v___x_3322_ = l_Lean_mkIdent(v_auxFunName_3300_);
v___x_3323_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3321_, v___x_3322_, v___x_3316_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3325_ = l_Array_append___redArg(v___x_3315_, v_binders_3304_);
lean_dec_ref(v_binders_3304_);
v___x_3326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3311_);
lean_ctor_set(v___x_3326_, 1, v___x_3314_);
lean_ctor_set(v___x_3326_, 2, v___x_3325_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3311_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3310_);
lean_inc(v_quotContext_3309_);
v___x_3332_ = l_Lean_addMacroScope(v_quotContext_3309_, v___x_3331_, v_currMacroScope_3310_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 3);
lean_ctor_set(v___x_3306_, 3, v___x_3333_);
lean_ctor_set(v___x_3306_, 2, v___x_3332_);
lean_ctor_set(v___x_3306_, 1, v___x_3330_);
lean_ctor_set(v___x_3306_, 0, v___x_3311_);
v___x_3335_ = v___x_3306_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_inc_n(v___x_3311_, 7);
v___x_3336_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3327_, v___x_3329_, v___x_3335_);
v___x_3337_ = l_Lean_Syntax_node1(v___x_3311_, v___x_3314_, v___x_3336_);
v___x_3338_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3324_, v___x_3326_, v___x_3337_);
v___x_3339_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3311_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3316_, 3);
v___x_3343_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3342_, v___x_3316_, v___x_3316_);
v___x_3344_ = l_Lean_Syntax_node4(v___x_3311_, v___x_3339_, v___x_3341_, v_body_3302_, v___x_3343_, v___x_3316_);
v___x_3345_ = l_Lean_Syntax_node5(v___x_3311_, v___x_3318_, v___x_3320_, v___x_3323_, v___x_3338_, v___x_3344_, v___x_3316_);
v___x_3346_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3312_, v___x_3317_, v___x_3345_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3346_);
v___x_3348_ = v___x_3297_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_binders_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3408_; 
v_binders_3355_ = lean_ctor_get(v_a_3295_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3295_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3409_ = lean_ctor_get(v_a_3295_, 3);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_a_3295_, 2);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_a_3295_, 1);
lean_dec(v_unused_3411_);
v___x_3357_ = v_a_3295_;
v_isShared_3358_ = v_isSharedCheck_3408_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_binders_3355_);
lean_dec(v_a_3295_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3408_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_ref_3359_; lean_object* v_quotContext_3360_; lean_object* v_currMacroScope_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v_ref_3359_ = lean_ctor_get(v___y_3303_, 5);
v_quotContext_3360_ = lean_ctor_get(v___y_3303_, 10);
v_currMacroScope_3361_ = lean_ctor_get(v___y_3303_, 11);
v___x_3362_ = 0;
v___x_3363_ = l_Lean_SourceInfo_fromRef(v_ref_3359_, v___x_3362_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3367_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3363_, 10);
v___x_3368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3363_);
lean_ctor_set(v___x_3368_, 1, v___x_3366_);
lean_ctor_set(v___x_3368_, 2, v___x_3367_);
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27));
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28));
v___x_3371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3363_);
lean_ctor_set(v___x_3371_, 1, v___x_3369_);
v___x_3372_ = l_Lean_Syntax_node1(v___x_3363_, v___x_3370_, v___x_3371_);
v___x_3373_ = l_Lean_Syntax_node1(v___x_3363_, v___x_3366_, v___x_3372_);
lean_inc_ref_n(v___x_3368_, 7);
v___x_3374_ = l_Lean_Syntax_node7(v___x_3363_, v___x_3365_, v___x_3368_, v___x_3368_, v___x_3368_, v___x_3368_, v___x_3368_, v___x_3368_, v___x_3373_);
v___x_3375_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3363_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3300_);
v___x_3379_ = l_Lean_mkIdent(v_auxFunName_3300_);
v___x_3380_ = l_Lean_Syntax_node2(v___x_3363_, v___x_3378_, v___x_3379_, v___x_3368_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3382_ = l_Array_append___redArg(v___x_3367_, v_binders_3355_);
lean_dec_ref(v_binders_3355_);
v___x_3383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3363_);
lean_ctor_set(v___x_3383_, 1, v___x_3366_);
lean_ctor_set(v___x_3383_, 2, v___x_3382_);
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3385_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3363_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3361_);
lean_inc(v_quotContext_3360_);
v___x_3389_ = l_Lean_addMacroScope(v_quotContext_3360_, v___x_3388_, v_currMacroScope_3361_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 3);
lean_ctor_set(v___x_3357_, 3, v___x_3390_);
lean_ctor_set(v___x_3357_, 2, v___x_3389_);
lean_ctor_set(v___x_3357_, 1, v___x_3387_);
lean_ctor_set(v___x_3357_, 0, v___x_3363_);
v___x_3392_ = v___x_3357_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_inc_n(v___x_3363_, 7);
v___x_3393_ = l_Lean_Syntax_node2(v___x_3363_, v___x_3384_, v___x_3386_, v___x_3392_);
v___x_3394_ = l_Lean_Syntax_node1(v___x_3363_, v___x_3366_, v___x_3393_);
v___x_3395_ = l_Lean_Syntax_node2(v___x_3363_, v___x_3381_, v___x_3383_, v___x_3394_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3363_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3368_, 3);
v___x_3400_ = l_Lean_Syntax_node2(v___x_3363_, v___x_3399_, v___x_3368_, v___x_3368_);
v___x_3401_ = l_Lean_Syntax_node4(v___x_3363_, v___x_3396_, v___x_3398_, v_body_3302_, v___x_3400_, v___x_3368_);
v___x_3402_ = l_Lean_Syntax_node5(v___x_3363_, v___x_3375_, v___x_3377_, v___x_3380_, v___x_3395_, v___x_3401_, v___x_3368_);
v___x_3403_ = l_Lean_Syntax_node2(v___x_3363_, v___x_3364_, v___x_3374_, v___x_3402_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3403_);
v___x_3405_ = v___x_3297_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_a_3430_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3294_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3294_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object* v_ctx_3438_, lean_object* v_i_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3438_, v_i_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_i_3439_);
lean_dec_ref(v_ctx_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_3448_, lean_object* v_ctx_3449_, lean_object* v_a_3450_, lean_object* v_b_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_nat_dec_lt(v_a_3450_, v_upperBound_3448_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec(v_a_3450_);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_b_3451_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; 
v___x_3461_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3449_, v_a_3450_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = lean_array_push(v_b_3451_, v_a_3462_);
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_nat_add(v_a_3450_, v___x_3464_);
lean_dec(v_a_3450_);
v_a_3450_ = v___x_3465_;
v_b_3451_ = v___x_3463_;
goto _start;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v_b_3451_);
lean_dec(v_a_3450_);
v_a_3467_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3461_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3461_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_3475_, lean_object* v_ctx_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3475_, v_ctx_3476_, v_a_3477_, v_b_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_ctx_3476_);
lean_dec(v_upperBound_3475_);
return v_res_3486_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4));
v___x_3501_ = l_String_toRawSubstring_x27(v___x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object* v_ctx_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_typeInfos_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_auxDefs_3527_; lean_object* v___x_3528_; 
v_typeInfos_3524_ = lean_ctor_get(v_ctx_3516_, 1);
v___x_3525_ = lean_array_get_size(v_typeInfos_3524_);
v___x_3526_ = lean_unsigned_to_nat(0u);
v_auxDefs_3527_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_3528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v___x_3525_, v_ctx_3516_, v___x_3526_, v_auxDefs_3527_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3564_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3564_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3564_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_ref_3533_; lean_object* v_quotContext_3534_; lean_object* v_currMacroScope_3535_; uint8_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
v_ref_3533_ = lean_ctor_get(v_a_3521_, 5);
v_quotContext_3534_ = lean_ctor_get(v_a_3521_, 10);
v_currMacroScope_3535_ = lean_ctor_get(v_a_3521_, 11);
v___x_3536_ = 0;
v___x_3537_ = l_Lean_SourceInfo_fromRef(v_ref_3533_, v___x_3536_);
v___x_3538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0));
v___x_3539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1));
lean_inc_n(v___x_3537_, 8);
v___x_3540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3537_);
lean_ctor_set(v___x_3540_, 1, v___x_3538_);
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2));
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3));
v___x_3544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3537_);
lean_ctor_set(v___x_3544_, 1, v___x_3542_);
v___x_3545_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5);
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_3535_);
lean_inc(v_quotContext_3534_);
v___x_3547_ = l_Lean_addMacroScope(v_quotContext_3534_, v___x_3546_, v_currMacroScope_3535_);
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10));
v___x_3549_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3537_);
lean_ctor_set(v___x_3549_, 1, v___x_3545_);
lean_ctor_set(v___x_3549_, 2, v___x_3547_);
lean_ctor_set(v___x_3549_, 3, v___x_3548_);
v___x_3550_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_3551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3537_);
lean_ctor_set(v___x_3551_, 1, v___x_3541_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
v___x_3552_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_3553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3537_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_Syntax_node4(v___x_3537_, v___x_3543_, v___x_3544_, v___x_3549_, v___x_3551_, v___x_3553_);
v___x_3555_ = l_Array_mkArray1___redArg(v___x_3554_);
v___x_3556_ = l_Array_append___redArg(v___x_3555_, v_a_3529_);
lean_dec(v_a_3529_);
v___x_3557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3537_);
lean_ctor_set(v___x_3557_, 1, v___x_3541_);
lean_ctor_set(v___x_3557_, 2, v___x_3556_);
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11));
v___x_3559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3537_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l_Lean_Syntax_node3(v___x_3537_, v___x_3539_, v___x_3540_, v___x_3557_, v___x_3559_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3560_);
v___x_3562_ = v___x_3531_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
v_a_3565_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3528_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3528_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object* v_ctx_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec_ref(v_ctx_3573_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object* v_upperBound_3582_, lean_object* v_ctx_3583_, lean_object* v_inst_3584_, lean_object* v_R_3585_, lean_object* v_a_3586_, lean_object* v_b_3587_, lean_object* v_c_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3582_, v_ctx_3583_, v_a_3586_, v_b_3587_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_3597_, lean_object* v_ctx_3598_, lean_object* v_inst_3599_, lean_object* v_R_3600_, lean_object* v_a_3601_, lean_object* v_b_3602_, lean_object* v_c_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(v_upperBound_3597_, v_ctx_3598_, v_inst_3599_, v_R_3600_, v_a_3601_, v_b_3602_, v_c_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v_ctx_3598_);
lean_dec(v_upperBound_3597_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
if (lean_obj_tag(v_a_3612_) == 0)
{
lean_object* v___x_3614_; 
v___x_3614_ = l_List_reverse___redArg(v_a_3613_);
return v___x_3614_;
}
else
{
lean_object* v_head_3615_; lean_object* v_tail_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3625_; 
v_head_3615_ = lean_ctor_get(v_a_3612_, 0);
v_tail_3616_ = lean_ctor_get(v_a_3612_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_a_3612_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3618_ = v_a_3612_;
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_tail_3616_);
lean_inc(v_head_3615_);
lean_dec(v_a_3612_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3620_ = l_Lean_MessageData_ofSyntax(v_head_3615_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v_a_3613_);
lean_ctor_set(v___x_3618_, 0, v___x_3620_);
v___x_3622_ = v___x_3618_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_a_3613_);
v___x_3622_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
v_a_3612_ = v_tail_3616_;
v_a_3613_ = v___x_3622_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3626_; double v___x_3627_; 
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = lean_float_of_nat(v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object* v_cls_3630_, lean_object* v_msg_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_ref_3637_; lean_object* v___x_3638_; lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3683_; 
v_ref_3637_ = lean_ctor_get(v___y_3634_, 5);
v___x_3638_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3683_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3683_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v_traceState_3644_; lean_object* v_env_3645_; lean_object* v_nextMacroScope_3646_; lean_object* v_ngen_3647_; lean_object* v_auxDeclNGen_3648_; lean_object* v_cache_3649_; lean_object* v_messages_3650_; lean_object* v_infoState_3651_; lean_object* v_snapshotTasks_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3682_; 
v___x_3643_ = lean_st_ref_take(v___y_3635_);
v_traceState_3644_ = lean_ctor_get(v___x_3643_, 4);
v_env_3645_ = lean_ctor_get(v___x_3643_, 0);
v_nextMacroScope_3646_ = lean_ctor_get(v___x_3643_, 1);
v_ngen_3647_ = lean_ctor_get(v___x_3643_, 2);
v_auxDeclNGen_3648_ = lean_ctor_get(v___x_3643_, 3);
v_cache_3649_ = lean_ctor_get(v___x_3643_, 5);
v_messages_3650_ = lean_ctor_get(v___x_3643_, 6);
v_infoState_3651_ = lean_ctor_get(v___x_3643_, 7);
v_snapshotTasks_3652_ = lean_ctor_get(v___x_3643_, 8);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3654_ = v___x_3643_;
v_isShared_3655_ = v_isSharedCheck_3682_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_snapshotTasks_3652_);
lean_inc(v_infoState_3651_);
lean_inc(v_messages_3650_);
lean_inc(v_cache_3649_);
lean_inc(v_traceState_3644_);
lean_inc(v_auxDeclNGen_3648_);
lean_inc(v_ngen_3647_);
lean_inc(v_nextMacroScope_3646_);
lean_inc(v_env_3645_);
lean_dec(v___x_3643_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3682_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
uint64_t v_tid_3656_; lean_object* v_traces_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3681_; 
v_tid_3656_ = lean_ctor_get_uint64(v_traceState_3644_, sizeof(void*)*1);
v_traces_3657_ = lean_ctor_get(v_traceState_3644_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_traceState_3644_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3659_ = v_traceState_3644_;
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_traces_3657_);
lean_dec(v_traceState_3644_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; double v___x_3662_; uint8_t v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3661_ = lean_box(0);
v___x_3662_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0);
v___x_3663_ = 0;
v___x_3664_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_3665_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3665_, 0, v_cls_3630_);
lean_ctor_set(v___x_3665_, 1, v___x_3661_);
lean_ctor_set(v___x_3665_, 2, v___x_3664_);
lean_ctor_set_float(v___x_3665_, sizeof(void*)*3, v___x_3662_);
lean_ctor_set_float(v___x_3665_, sizeof(void*)*3 + 8, v___x_3662_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*3 + 16, v___x_3663_);
v___x_3666_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1));
v___x_3667_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v_a_3639_);
lean_ctor_set(v___x_3667_, 2, v___x_3666_);
lean_inc(v_ref_3637_);
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_ref_3637_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_PersistentArray_push___redArg(v_traces_3657_, v___x_3668_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v___x_3669_);
v___x_3671_ = v___x_3659_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3669_);
lean_ctor_set_uint64(v_reuseFailAlloc_3680_, sizeof(void*)*1, v_tid_3656_);
v___x_3671_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v___x_3671_);
v___x_3673_ = v___x_3654_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_env_3645_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_nextMacroScope_3646_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_ngen_3647_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_auxDeclNGen_3648_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v___x_3671_);
lean_ctor_set(v_reuseFailAlloc_3679_, 5, v_cache_3649_);
lean_ctor_set(v_reuseFailAlloc_3679_, 6, v_messages_3650_);
lean_ctor_set(v_reuseFailAlloc_3679_, 7, v_infoState_3651_);
lean_ctor_set(v_reuseFailAlloc_3679_, 8, v_snapshotTasks_3652_);
v___x_3673_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3674_ = lean_st_ref_set(v___y_3635_, v___x_3673_);
v___x_3675_ = lean_box(0);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3675_);
v___x_3677_ = v___x_3641_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3684_, lean_object* v_msg_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3684_, v_msg_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2));
v___x_3701_ = l_Lean_Name_append(v___x_3700_, v___x_3699_);
return v___x_3701_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4));
v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object* v_ctx_3705_, lean_object* v_declName_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3705_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3714_, 1);
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3718_ = lean_mk_empty_array_with_capacity(v___x_3717_);
lean_inc_ref(v___x_3718_);
v___x_3719_ = lean_array_push(v___x_3718_, v_declName_3706_);
v___x_3720_ = 1;
v___x_3721_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3705_, v___x_3716_, v___x_3719_, v___x_3720_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
lean_dec_ref(v___x_3719_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_options_3722_; lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3763_; 
v_options_3722_ = lean_ctor_get(v_a_3711_, 2);
v_a_3723_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3725_ = v___x_3721_;
v_isShared_3726_ = v_isSharedCheck_3763_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3721_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3763_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_inheritedTraceOptions_3727_; uint8_t v_hasTrace_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_inheritedTraceOptions_3727_ = lean_ctor_get(v_a_3711_, 13);
v_hasTrace_3728_ = lean_ctor_get_uint8(v_options_3722_, sizeof(void*)*1);
v___x_3729_ = lean_array_push(v___x_3718_, v_a_3715_);
v___x_3730_ = l_Array_append___redArg(v___x_3729_, v_a_3723_);
lean_dec(v_a_3723_);
if (v_hasTrace_3728_ == 0)
{
lean_object* v___x_3732_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3730_);
v___x_3732_ = v___x_3725_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3735_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3727_, v_options_3722_, v___x_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3738_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3730_);
v___x_3738_ = v___x_3725_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3730_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_del_object(v___x_3725_);
v___x_3740_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3730_);
v___x_3741_ = lean_array_to_list(v___x_3730_);
v___x_3742_ = lean_box(0);
v___x_3743_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3741_, v___x_3742_);
v___x_3744_ = l_Lean_MessageData_ofList(v___x_3743_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3740_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3734_, v___x_3745_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v___x_3746_, 0);
lean_dec(v_unused_3754_);
v___x_3748_ = v___x_3746_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_dec(v___x_3746_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3730_);
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3730_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v___x_3730_);
v_a_3755_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3746_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3746_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v___x_3718_);
lean_dec(v_a_3715_);
v_a_3764_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3721_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3721_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v_declName_3706_);
lean_dec_ref(v_ctx_3705_);
v_a_3772_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3714_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3714_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object* v_ctx_3780_, lean_object* v_declName_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_ctx_3780_, v_declName_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object* v_cls_3790_, lean_object* v_msg_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3790_, v_msg_3791_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object* v_cls_3800_, lean_object* v_msg_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(v_cls_3800_, v_msg_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2));
v___x_3818_ = l_String_toRawSubstring_x27(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5));
v___x_3823_ = l_String_toRawSubstring_x27(v___x_3822_);
return v___x_3823_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11));
v___x_3837_ = l_String_toRawSubstring_x27(v___x_3836_);
return v___x_3837_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15));
v___x_3844_ = l_String_toRawSubstring_x27(v___x_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object* v_ctx_3848_, lean_object* v_name_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v_auxFunNames_3852_; lean_object* v_ref_3853_; lean_object* v_quotContext_3854_; lean_object* v_currMacroScope_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v_auxFunName_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_auxFunNames_3852_ = lean_ctor_get(v_ctx_3848_, 2);
v_ref_3853_ = lean_ctor_get(v_a_3850_, 5);
v_quotContext_3854_ = lean_ctor_get(v_a_3850_, 10);
v_currMacroScope_3855_ = lean_ctor_get(v_a_3850_, 11);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_unsigned_to_nat(0u);
v_auxFunName_3858_ = lean_array_get_borrowed(v___x_3856_, v_auxFunNames_3852_, v___x_3857_);
v___x_3859_ = 0;
v___x_3860_ = l_Lean_SourceInfo_fromRef(v_ref_3853_, v___x_3859_);
v___x_3861_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3863_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3864_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3860_, 25);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3860_);
lean_ctor_set(v___x_3865_, 1, v___x_3863_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
lean_inc_ref_n(v___x_3865_, 12);
v___x_3866_ = l_Lean_Syntax_node7(v___x_3860_, v___x_3862_, v___x_3865_, v___x_3865_, v___x_3865_, v___x_3865_, v___x_3865_, v___x_3865_, v___x_3865_);
v___x_3867_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3860_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3858_);
v___x_3871_ = l_Lean_mkIdent(v_auxFunName_3858_);
v___x_3872_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3870_, v___x_3871_, v___x_3865_);
v___x_3873_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1));
v___x_3875_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_3876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3860_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3);
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3855_, 5);
lean_inc_n(v_quotContext_3854_, 5);
v___x_3879_ = l_Lean_addMacroScope(v_quotContext_3854_, v___x_3878_, v_currMacroScope_3855_);
v___x_3880_ = lean_box(0);
v___x_3881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3860_);
lean_ctor_set(v___x_3881_, 1, v___x_3877_);
lean_ctor_set(v___x_3881_, 2, v___x_3879_);
lean_ctor_set(v___x_3881_, 3, v___x_3880_);
v___x_3882_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7));
v___x_3884_ = l_Lean_addMacroScope(v_quotContext_3854_, v___x_3883_, v_currMacroScope_3855_);
v___x_3885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3860_);
lean_ctor_set(v___x_3885_, 1, v___x_3882_);
lean_ctor_set(v___x_3885_, 2, v___x_3884_);
lean_ctor_set(v___x_3885_, 3, v___x_3880_);
v___x_3886_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3863_, v___x_3881_, v___x_3885_);
v___x_3887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3860_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_mkCIdent(v_name_3849_);
lean_inc_ref(v___x_3888_);
v___x_3890_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3863_, v___x_3888_, v___x_3889_);
v___x_3891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_3892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3860_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_Syntax_node5(v___x_3860_, v___x_3874_, v___x_3876_, v___x_3886_, v___x_3890_, v___x_3865_, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_node1(v___x_3860_, v___x_3863_, v___x_3893_);
v___x_3895_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3896_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
v___x_3898_ = l_Lean_addMacroScope(v_quotContext_3854_, v___x_3897_, v_currMacroScope_3855_);
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10));
v___x_3900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3860_);
lean_ctor_set(v___x_3900_, 1, v___x_3896_);
lean_ctor_set(v___x_3900_, 2, v___x_3898_);
lean_ctor_set(v___x_3900_, 3, v___x_3899_);
v___x_3901_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3895_, v___x_3888_, v___x_3900_);
v___x_3902_ = l_Lean_Syntax_node1(v___x_3860_, v___x_3863_, v___x_3901_);
v___x_3903_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3873_, v___x_3894_, v___x_3902_);
v___x_3904_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3860_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_3908_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12);
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14));
v___x_3910_ = l_Lean_addMacroScope(v_quotContext_3854_, v___x_3909_, v_currMacroScope_3855_);
v___x_3911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3860_);
lean_ctor_set(v___x_3911_, 1, v___x_3908_);
lean_ctor_set(v___x_3911_, 2, v___x_3910_);
lean_ctor_set(v___x_3911_, 3, v___x_3880_);
v___x_3912_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_3913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3860_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17));
v___x_3916_ = l_Lean_addMacroScope(v_quotContext_3854_, v___x_3915_, v_currMacroScope_3855_);
v___x_3917_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3860_);
lean_ctor_set(v___x_3917_, 1, v___x_3914_);
lean_ctor_set(v___x_3917_, 2, v___x_3916_);
lean_ctor_set(v___x_3917_, 3, v___x_3880_);
v___x_3918_ = l_Lean_Syntax_node3(v___x_3860_, v___x_3907_, v___x_3911_, v___x_3913_, v___x_3917_);
v___x_3919_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
v___x_3920_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3919_, v___x_3865_, v___x_3865_);
v___x_3921_ = l_Lean_Syntax_node4(v___x_3860_, v___x_3904_, v___x_3906_, v___x_3918_, v___x_3920_, v___x_3865_);
v___x_3922_ = l_Lean_Syntax_node5(v___x_3860_, v___x_3867_, v___x_3869_, v___x_3872_, v___x_3903_, v___x_3921_, v___x_3865_);
v___x_3923_ = l_Lean_Syntax_node2(v___x_3860_, v___x_3861_, v___x_3866_, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object* v_ctx_3925_, lean_object* v_name_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3925_, v_name_3926_, v_a_3927_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_ctx_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object* v_ctx_3930_, lean_object* v_name_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3930_, v_name_3931_, v_a_3936_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object* v_ctx_3940_, lean_object* v_name_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(v_ctx_3940_, v_name_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec_ref(v_ctx_3940_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object* v_ctx_3950_, lean_object* v_name_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v___x_3959_; lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; lean_object* v___x_3966_; 
lean_inc(v_name_3951_);
v___x_3959_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3950_, v_name_3951_, v_a_3956_);
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_mk_empty_array_with_capacity(v___x_3962_);
lean_inc_ref(v___x_3963_);
v___x_3964_ = lean_array_push(v___x_3963_, v_name_3951_);
v___x_3965_ = 1;
v___x_3966_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3950_, v___x_3961_, v___x_3964_, v___x_3965_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
lean_dec_ref(v___x_3964_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_options_3967_; lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4008_; 
v_options_3967_ = lean_ctor_get(v_a_3956_, 2);
v_a_3968_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3970_ = v___x_3966_;
v_isShared_3971_ = v_isSharedCheck_4008_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3966_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4008_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v_inheritedTraceOptions_3972_; uint8_t v_hasTrace_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_inheritedTraceOptions_3972_ = lean_ctor_get(v_a_3956_, 13);
v_hasTrace_3973_ = lean_ctor_get_uint8(v_options_3967_, sizeof(void*)*1);
v___x_3974_ = lean_array_push(v___x_3963_, v_a_3960_);
v___x_3975_ = l_Array_append___redArg(v___x_3974_, v_a_3968_);
lean_dec(v_a_3968_);
if (v_hasTrace_3973_ == 0)
{
lean_object* v___x_3977_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3975_);
v___x_3977_ = v___x_3970_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3979_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3980_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3972_, v_options_3967_, v___x_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3983_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3975_);
v___x_3983_ = v___x_3970_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3975_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_del_object(v___x_3970_);
v___x_3985_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3975_);
v___x_3986_ = lean_array_to_list(v___x_3975_);
v___x_3987_ = lean_box(0);
v___x_3988_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3986_, v___x_3987_);
v___x_3989_ = l_Lean_MessageData_ofList(v___x_3988_);
v___x_3990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3985_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3979_, v___x_3990_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; 
v_unused_3999_ = lean_ctor_get(v___x_3991_, 0);
lean_dec(v_unused_3999_);
v___x_3993_ = v___x_3991_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_dec(v___x_3991_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3975_);
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3975_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v___x_3975_);
v_a_4000_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3991_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3991_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec_ref(v___x_3963_);
lean_dec(v_a_3960_);
v_a_4009_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3966_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3966_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object* v_ctx_4017_, lean_object* v_name_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_ctx_4017_, v_name_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; lean_object* v_env_4030_; lean_object* v___x_4031_; lean_object* v_mainModule_4032_; lean_object* v___x_4033_; 
v___x_4029_ = lean_st_ref_get(v___y_4027_);
v_env_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc_ref(v_env_4030_);
lean_dec(v___x_4029_);
v___x_4031_ = l_Lean_Environment_header(v_env_4030_);
lean_dec_ref(v_env_4030_);
v_mainModule_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_mainModule_4032_);
lean_dec_ref(v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_mainModule_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4034_);
lean_dec(v___y_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4038_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t v_a_4045_, lean_object* v_a_4046_, lean_object* v_declName_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
if (v_a_4045_ == 0)
{
lean_object* v___x_4055_; 
v___x_4055_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_a_4046_, v_declName_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
return v___x_4055_;
}
else
{
lean_object* v___x_4056_; 
v___x_4056_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_a_4046_, v_declName_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_declName_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v_a_6412__boxed_4067_; lean_object* v_res_4068_; 
v_a_6412__boxed_4067_ = lean_unbox(v_a_4057_);
v_res_4068_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(v_a_6412__boxed_4067_, v_a_4058_, v_declName_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
lean_ctor_set(v___x_4074_, 2, v___x_4073_);
lean_ctor_set(v___x_4074_, 3, v___x_4073_);
lean_ctor_set(v___x_4074_, 4, v___x_4072_);
lean_ctor_set(v___x_4074_, 5, v___x_4072_);
lean_ctor_set(v___x_4074_, 6, v___x_4072_);
lean_ctor_set(v___x_4074_, 7, v___x_4072_);
lean_ctor_set(v___x_4074_, 8, v___x_4072_);
lean_ctor_set(v___x_4074_, 9, v___x_4072_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = lean_unsigned_to_nat(32u);
v___x_4076_ = lean_mk_empty_array_with_capacity(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4078_ = ((size_t)5ULL);
v___x_4079_ = lean_unsigned_to_nat(0u);
v___x_4080_ = lean_unsigned_to_nat(32u);
v___x_4081_ = lean_mk_empty_array_with_capacity(v___x_4080_);
v___x_4082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_4083_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
lean_ctor_set(v___x_4083_, 1, v___x_4081_);
lean_ctor_set(v___x_4083_, 2, v___x_4079_);
lean_ctor_set(v___x_4083_, 3, v___x_4079_);
lean_ctor_set_usize(v___x_4083_, 4, v___x_4078_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4084_ = lean_box(1);
v___x_4085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_4086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v___x_4085_);
lean_ctor_set(v___x_4087_, 2, v___x_4084_);
return v___x_4087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_4090_ = l_Lean_stringToMessageData(v___x_4089_);
return v___x_4090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_4093_ = l_Lean_stringToMessageData(v___x_4092_);
return v___x_4093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_4096_ = l_Lean_stringToMessageData(v___x_4095_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_4099_ = l_Lean_stringToMessageData(v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_4102_ = l_Lean_stringToMessageData(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_4108_ = l_Lean_stringToMessageData(v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_4109_, lean_object* v_declHint_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; lean_object* v_env_4114_; uint8_t v___y_4116_; uint8_t v___x_4172_; uint8_t v___x_4173_; 
v___x_4113_ = lean_st_ref_get(v___y_4111_);
v_env_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc_ref(v_env_4114_);
lean_dec(v___x_4113_);
v___x_4172_ = l_Lean_Name_isAnonymous(v_declHint_4110_);
v___x_4173_ = lean_bool_not(v___x_4172_);
if (v___x_4173_ == 0)
{
v___y_4116_ = v___x_4173_;
goto v___jp_4115_;
}
else
{
uint8_t v_isExporting_4174_; 
v_isExporting_4174_ = lean_ctor_get_uint8(v_env_4114_, sizeof(void*)*8);
v___y_4116_ = v_isExporting_4174_;
goto v___jp_4115_;
}
v___jp_4115_:
{
if (v___y_4116_ == 0)
{
lean_object* v___x_4117_; 
lean_dec_ref(v_env_4114_);
lean_dec(v_declHint_4110_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_msg_4109_);
return v___x_4117_;
}
else
{
uint8_t v___x_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
v___x_4118_ = 0;
lean_inc_ref(v_env_4114_);
v___x_4119_ = l_Lean_Environment_setExporting(v_env_4114_, v___x_4118_);
lean_inc(v_declHint_4110_);
lean_inc_ref(v___x_4119_);
v___x_4120_ = l_Lean_Environment_contains(v___x_4119_, v_declHint_4110_, v___y_4116_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; 
lean_dec_ref(v___x_4119_);
lean_dec_ref(v_env_4114_);
lean_dec(v_declHint_4110_);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_msg_4109_);
return v___x_4121_;
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v_c_4127_; lean_object* v___x_4128_; 
v___x_4122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4124_ = l_Lean_Options_empty;
v___x_4125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4119_);
lean_ctor_set(v___x_4125_, 1, v___x_4122_);
lean_ctor_set(v___x_4125_, 2, v___x_4123_);
lean_ctor_set(v___x_4125_, 3, v___x_4124_);
lean_inc(v_declHint_4110_);
v___x_4126_ = l_Lean_MessageData_ofConstName(v_declHint_4110_, v___x_4118_);
v_c_4127_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4127_, 0, v___x_4125_);
lean_ctor_set(v_c_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4114_, v_declHint_4110_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v_env_4114_);
lean_dec(v_declHint_4110_);
v___x_4129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
lean_ctor_set(v___x_4130_, 1, v_c_4127_);
v___x_4131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_MessageData_note(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v_msg_4109_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
else
{
lean_object* v_val_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4171_; 
v_val_4136_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4138_ = v___x_4128_;
v_isShared_4139_ = v_isSharedCheck_4171_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_val_4136_);
lean_dec(v___x_4128_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4171_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v_mod_4143_; uint8_t v___x_4144_; 
v___x_4140_ = lean_box(0);
v___x_4141_ = l_Lean_Environment_header(v_env_4114_);
lean_dec_ref(v_env_4114_);
v___x_4142_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4141_);
v_mod_4143_ = lean_array_get(v___x_4140_, v___x_4142_, v_val_4136_);
lean_dec(v_val_4136_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = l_Lean_isPrivateName(v_declHint_4110_);
lean_dec(v_declHint_4110_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v_c_4127_);
v___x_4147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_4148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_MessageData_ofName(v_mod_4143_);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4150_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = l_Lean_MessageData_note(v___x_4152_);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v_msg_4109_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set_tag(v___x_4138_, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4154_);
v___x_4156_ = v___x_4138_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v_c_4127_);
v___x_4160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_MessageData_ofName(v_mod_4143_);
v___x_4163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4161_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Lean_MessageData_note(v___x_4165_);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v_msg_4109_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set_tag(v___x_4138_, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4167_);
v___x_4169_ = v___x_4138_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_4175_, lean_object* v_declHint_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4175_, v_declHint_4176_, v___y_4177_);
lean_dec(v___y_4177_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_4180_, lean_object* v_declHint_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v___x_4185_; lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4195_; 
v___x_4185_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4180_, v_declHint_4181_, v___y_4183_);
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4190_ = l_Lean_unknownIdentifierMessageTag;
v___x_4191_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v_a_4186_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4191_);
v___x_4193_ = v___x_4188_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_4196_, lean_object* v_declHint_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4196_, v_declHint_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* v_msgData_4202_, lean_object* v_macroStack_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v_scopes_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v_opts_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; uint8_t v___x_4213_; 
v___x_4206_ = lean_st_ref_get(v___y_4204_);
v_scopes_4207_ = lean_ctor_get(v___x_4206_, 2);
lean_inc(v_scopes_4207_);
lean_dec(v___x_4206_);
v___x_4208_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4209_ = l_List_head_x21___redArg(v___x_4208_, v_scopes_4207_);
lean_dec(v_scopes_4207_);
v_opts_4210_ = lean_ctor_get(v___x_4209_, 1);
lean_inc_ref(v_opts_4210_);
lean_dec(v___x_4209_);
v___x_4211_ = l_Lean_Elab_pp_macroStack;
v___x_4212_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_4210_, v___x_4211_);
lean_dec_ref(v_opts_4210_);
v___x_4213_ = lean_bool_not(v___x_4212_);
if (v___x_4213_ == 0)
{
if (lean_obj_tag(v_macroStack_4203_) == 0)
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_msgData_4202_);
return v___x_4214_;
}
else
{
lean_object* v_head_4215_; lean_object* v_after_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4231_; 
v_head_4215_ = lean_ctor_get(v_macroStack_4203_, 0);
lean_inc(v_head_4215_);
v_after_4216_ = lean_ctor_get(v_head_4215_, 1);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_head_4215_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v_head_4215_, 0);
lean_dec(v_unused_4232_);
v___x_4218_ = v_head_4215_;
v_isShared_4219_ = v_isSharedCheck_4231_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_after_4216_);
lean_dec(v_head_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4231_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4220_; lean_object* v___x_4222_; 
v___x_4220_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_4219_ == 0)
{
lean_ctor_set_tag(v___x_4218_, 7);
lean_ctor_set(v___x_4218_, 1, v___x_4220_);
lean_ctor_set(v___x_4218_, 0, v_msgData_4202_);
v___x_4222_ = v___x_4218_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_msgData_4202_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v_msgData_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4223_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_4224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4222_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
v___x_4225_ = l_Lean_MessageData_ofSyntax(v_after_4216_);
v___x_4226_ = l_Lean_indentD(v___x_4225_);
v_msgData_4227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4227_, 0, v___x_4224_);
lean_ctor_set(v_msgData_4227_, 1, v___x_4226_);
v___x_4228_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_4227_, v_macroStack_4203_);
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
return v___x_4229_;
}
}
}
}
else
{
lean_object* v___x_4233_; 
lean_dec(v_macroStack_4203_);
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v_msgData_4202_);
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_4234_, lean_object* v_macroStack_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4234_, v_macroStack_4235_, v___y_4236_);
lean_dec(v___y_4236_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object* v_msgData_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; lean_object* v_env_4243_; lean_object* v___x_4244_; lean_object* v_scopes_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v_opts_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4242_ = lean_st_ref_get(v___y_4240_);
v_env_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc_ref(v_env_4243_);
lean_dec(v___x_4242_);
v___x_4244_ = lean_st_ref_get(v___y_4240_);
v_scopes_4245_ = lean_ctor_get(v___x_4244_, 2);
lean_inc(v_scopes_4245_);
lean_dec(v___x_4244_);
v___x_4246_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4247_ = l_List_head_x21___redArg(v___x_4246_, v_scopes_4245_);
lean_dec(v_scopes_4245_);
v_opts_4248_ = lean_ctor_get(v___x_4247_, 1);
lean_inc_ref(v_opts_4248_);
lean_dec(v___x_4247_);
v___x_4249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4250_ = lean_unsigned_to_nat(32u);
v___x_4251_ = lean_mk_empty_array_with_capacity(v___x_4250_);
lean_dec_ref(v___x_4251_);
v___x_4252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4253_, 0, v_env_4243_);
lean_ctor_set(v___x_4253_, 1, v___x_4249_);
lean_ctor_set(v___x_4253_, 2, v___x_4252_);
lean_ctor_set(v___x_4253_, 3, v_opts_4248_);
v___x_4254_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
lean_ctor_set(v___x_4254_, 1, v_msgData_4239_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4256_, v___y_4257_);
lean_dec(v___y_4257_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Elab_Command_getRef___redArg(v___y_4261_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v_macroStack_4266_; lean_object* v___x_4267_; lean_object* v_a_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4279_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v_macroStack_4266_ = lean_ctor_get(v___y_4261_, 4);
v___x_4267_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msg_4260_, v___y_4262_);
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref(v___x_4267_);
v___x_4269_ = l_Lean_Elab_getBetterRef(v_a_4265_, v_macroStack_4266_);
lean_dec(v_a_4265_);
lean_inc(v_macroStack_4266_);
v___x_4270_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_a_4268_, v_macroStack_4266_, v___y_4262_);
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4279_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4279_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4269_);
lean_ctor_set(v___x_4275_, 1, v_a_4271_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set_tag(v___x_4273_, 1);
lean_ctor_set(v___x_4273_, 0, v___x_4275_);
v___x_4277_ = v___x_4273_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v_msg_4260_);
v_a_4280_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4264_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4264_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_4293_, lean_object* v_msg_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Elab_Command_getRef___redArg(v___y_4295_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v_fileName_4300_; lean_object* v_fileMap_4301_; lean_object* v_currRecDepth_4302_; lean_object* v_cmdPos_4303_; lean_object* v_macroStack_4304_; lean_object* v_quotContext_x3f_4305_; lean_object* v_currMacroScope_4306_; lean_object* v_snap_x3f_4307_; lean_object* v_cancelTk_x3f_4308_; uint8_t v_suppressElabErrors_4309_; lean_object* v_ref_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v_fileName_4300_ = lean_ctor_get(v___y_4295_, 0);
v_fileMap_4301_ = lean_ctor_get(v___y_4295_, 1);
v_currRecDepth_4302_ = lean_ctor_get(v___y_4295_, 2);
v_cmdPos_4303_ = lean_ctor_get(v___y_4295_, 3);
v_macroStack_4304_ = lean_ctor_get(v___y_4295_, 4);
v_quotContext_x3f_4305_ = lean_ctor_get(v___y_4295_, 5);
v_currMacroScope_4306_ = lean_ctor_get(v___y_4295_, 6);
v_snap_x3f_4307_ = lean_ctor_get(v___y_4295_, 8);
v_cancelTk_x3f_4308_ = lean_ctor_get(v___y_4295_, 9);
v_suppressElabErrors_4309_ = lean_ctor_get_uint8(v___y_4295_, sizeof(void*)*10);
v_ref_4310_ = l_Lean_replaceRef(v_ref_4293_, v_a_4299_);
lean_dec(v_a_4299_);
lean_inc(v_cancelTk_x3f_4308_);
lean_inc(v_snap_x3f_4307_);
lean_inc(v_currMacroScope_4306_);
lean_inc(v_quotContext_x3f_4305_);
lean_inc(v_macroStack_4304_);
lean_inc(v_cmdPos_4303_);
lean_inc(v_currRecDepth_4302_);
lean_inc_ref(v_fileMap_4301_);
lean_inc_ref(v_fileName_4300_);
v___x_4311_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4311_, 0, v_fileName_4300_);
lean_ctor_set(v___x_4311_, 1, v_fileMap_4301_);
lean_ctor_set(v___x_4311_, 2, v_currRecDepth_4302_);
lean_ctor_set(v___x_4311_, 3, v_cmdPos_4303_);
lean_ctor_set(v___x_4311_, 4, v_macroStack_4304_);
lean_ctor_set(v___x_4311_, 5, v_quotContext_x3f_4305_);
lean_ctor_set(v___x_4311_, 6, v_currMacroScope_4306_);
lean_ctor_set(v___x_4311_, 7, v_ref_4310_);
lean_ctor_set(v___x_4311_, 8, v_snap_x3f_4307_);
lean_ctor_set(v___x_4311_, 9, v_cancelTk_x3f_4308_);
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*10, v_suppressElabErrors_4309_);
v___x_4312_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4294_, v___x_4311_, v___y_4296_);
lean_dec_ref_known(v___x_4311_, 10);
return v___x_4312_;
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec_ref(v_msg_4294_);
v_a_4313_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4298_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4298_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_4321_, lean_object* v_msg_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4321_, v_msg_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v_ref_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_4327_, lean_object* v_msg_4328_, lean_object* v_declHint_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; lean_object* v_a_4334_; lean_object* v___x_4335_; 
v___x_4333_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4328_, v_declHint_4329_, v___y_4330_, v___y_4331_);
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4327_, v_a_4334_, v___y_4330_, v___y_4331_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_4336_, lean_object* v_msg_4337_, lean_object* v_declHint_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4336_, v_msg_4337_, v_declHint_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v_ref_4336_);
return v_res_4342_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0));
v___x_4345_ = l_Lean_stringToMessageData(v___x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_4346_, lean_object* v_constName_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4351_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4352_ = 0;
lean_inc(v_constName_4347_);
v___x_4353_ = l_Lean_MessageData_ofConstName(v_constName_4347_, v___x_4352_);
v___x_4354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4351_);
lean_ctor_set(v___x_4354_, 1, v___x_4353_);
v___x_4355_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_4356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4346_, v___x_4356_, v_constName_4347_, v___y_4348_, v___y_4349_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_4358_, lean_object* v_constName_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4358_, v_constName_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v_ref_4358_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_constName_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l_Lean_Elab_Command_getRef___redArg(v___y_4365_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_a_4369_, v_constName_4364_, v___y_4365_, v___y_4366_);
lean_dec(v_a_4369_);
return v___x_4370_;
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_constName_4364_);
v_a_4371_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4368_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4368_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_constName_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4379_, v___y_4380_, v___y_4381_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object* v_constName_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; lean_object* v_env_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; 
v___x_4388_ = lean_st_ref_get(v___y_4386_);
v_env_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc_ref(v_env_4389_);
lean_dec(v___x_4388_);
v___x_4390_ = 0;
lean_inc(v_constName_4384_);
v___x_4391_ = l_Lean_Environment_find_x3f(v_env_4389_, v_constName_4384_, v___x_4390_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4384_, v___y_4385_, v___y_4386_);
return v___x_4392_;
}
else
{
lean_object* v_val_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_constName_4384_);
v_val_4393_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4391_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_val_4393_);
lean_dec(v___x_4391_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 0);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_val_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object* v_constName_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_constName_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(lean_object* v_x_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
if (lean_obj_tag(v_x_4406_) == 0)
{
uint8_t v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = 1;
v___x_4411_ = lean_box(v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
return v___x_4412_;
}
else
{
lean_object* v_head_4413_; lean_object* v_tail_4414_; lean_object* v___x_4415_; 
v_head_4413_ = lean_ctor_get(v_x_4406_, 0);
lean_inc(v_head_4413_);
v_tail_4414_ = lean_ctor_get(v_x_4406_, 1);
lean_inc(v_tail_4414_);
lean_dec_ref_known(v_x_4406_, 2);
v___x_4415_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_head_4413_, v___y_4407_, v___y_4408_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4434_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4434_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4434_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
if (lean_obj_tag(v_a_4416_) == 6)
{
lean_object* v_val_4420_; lean_object* v_numFields_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v_val_4420_ = lean_ctor_get(v_a_4416_, 0);
lean_inc_ref(v_val_4420_);
lean_dec_ref_known(v_a_4416_, 1);
v_numFields_4421_ = lean_ctor_get(v_val_4420_, 4);
lean_inc(v_numFields_4421_);
lean_dec_ref(v_val_4420_);
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = lean_nat_dec_eq(v_numFields_4421_, v___x_4422_);
lean_dec(v_numFields_4421_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
lean_dec(v_tail_4414_);
v___x_4424_ = lean_box(v___x_4423_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4424_);
v___x_4426_ = v___x_4418_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
else
{
lean_del_object(v___x_4418_);
v_x_4406_ = v_tail_4414_;
goto _start;
}
}
else
{
uint8_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4432_; 
lean_dec(v_a_4416_);
lean_dec(v_tail_4414_);
v___x_4429_ = 0;
v___x_4430_ = lean_box(v___x_4429_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4430_);
v___x_4432_ = v___x_4418_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_tail_4414_);
v_a_4435_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4415_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4415_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object* v_x_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v_x_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object* v_declName_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_declName_4448_, v___y_4449_, v___y_4450_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4509_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4455_ = v___x_4452_;
v_isShared_4456_ = v_isSharedCheck_4509_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4509_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
if (lean_obj_tag(v_a_4453_) == 5)
{
lean_object* v_val_4457_; lean_object* v_toConstantVal_4458_; lean_object* v_numParams_4459_; lean_object* v_numIndices_4460_; lean_object* v_ctors_4461_; uint8_t v_isRec_4462_; uint8_t v_isUnsafe_4463_; uint8_t v___y_4465_; lean_object* v_type_4498_; uint8_t v___x_4499_; uint8_t v___x_4500_; 
v_val_4457_ = lean_ctor_get(v_a_4453_, 0);
lean_inc_ref(v_val_4457_);
lean_dec_ref_known(v_a_4453_, 1);
v_toConstantVal_4458_ = lean_ctor_get(v_val_4457_, 0);
v_numParams_4459_ = lean_ctor_get(v_val_4457_, 1);
lean_inc(v_numParams_4459_);
v_numIndices_4460_ = lean_ctor_get(v_val_4457_, 2);
lean_inc(v_numIndices_4460_);
v_ctors_4461_ = lean_ctor_get(v_val_4457_, 4);
lean_inc(v_ctors_4461_);
v_isRec_4462_ = lean_ctor_get_uint8(v_val_4457_, sizeof(void*)*6);
v_isUnsafe_4463_ = lean_ctor_get_uint8(v_val_4457_, sizeof(void*)*6 + 1);
v_type_4498_ = lean_ctor_get(v_toConstantVal_4458_, 2);
v___x_4499_ = l_Lean_Expr_isProp(v_type_4498_);
v___x_4500_ = lean_bool_not(v___x_4499_);
if (v___x_4500_ == 0)
{
lean_dec_ref(v_val_4457_);
v___y_4465_ = v___x_4500_;
goto v___jp_4464_;
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4501_ = l_Lean_InductiveVal_numTypeFormers(v_val_4457_);
lean_dec_ref(v_val_4457_);
v___x_4502_ = lean_unsigned_to_nat(1u);
v___x_4503_ = lean_nat_dec_eq(v___x_4501_, v___x_4502_);
lean_dec(v___x_4501_);
v___y_4465_ = v___x_4503_;
goto v___jp_4464_;
}
v___jp_4464_:
{
if (v___y_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec(v_ctors_4461_);
lean_dec(v_numIndices_4460_);
lean_dec(v_numParams_4459_);
v___x_4466_ = lean_box(v___y_4465_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4466_);
v___x_4468_ = v___x_4455_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
else
{
lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = lean_nat_dec_eq(v_numIndices_4460_, v___x_4470_);
lean_dec(v_numIndices_4460_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; lean_object* v___x_4474_; 
lean_dec(v_ctors_4461_);
lean_dec(v_numParams_4459_);
v___x_4472_ = lean_box(v___x_4471_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4472_);
v___x_4474_ = v___x_4455_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4472_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
else
{
uint8_t v___x_4476_; 
v___x_4476_ = lean_nat_dec_eq(v_numParams_4459_, v___x_4470_);
lean_dec(v_numParams_4459_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
lean_dec(v_ctors_4461_);
v___x_4477_ = lean_box(v___x_4476_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4477_);
v___x_4479_ = v___x_4455_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
else
{
uint8_t v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = l_List_isEmpty___redArg(v_ctors_4461_);
v___x_4482_ = lean_bool_not(v___x_4481_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
lean_dec(v_ctors_4461_);
v___x_4483_ = lean_box(v___x_4482_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4483_);
v___x_4485_ = v___x_4455_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
else
{
uint8_t v___x_4487_; 
v___x_4487_ = lean_bool_not(v_isRec_4462_);
if (v___x_4487_ == 0)
{
lean_object* v___x_4488_; lean_object* v___x_4490_; 
lean_dec(v_ctors_4461_);
v___x_4488_ = lean_box(v___x_4487_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4488_);
v___x_4490_ = v___x_4455_;
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
else
{
uint8_t v___x_4492_; 
v___x_4492_ = lean_bool_not(v_isUnsafe_4463_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4495_; 
lean_dec(v_ctors_4461_);
v___x_4493_ = lean_box(v___x_4492_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4493_);
v___x_4495_ = v___x_4455_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
else
{
lean_object* v___x_4497_; 
lean_del_object(v___x_4455_);
v___x_4497_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v_ctors_4461_, v___y_4449_, v___y_4450_);
return v___x_4497_;
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
uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4507_; 
lean_dec(v_a_4453_);
v___x_4504_ = 0;
v___x_4505_ = lean_box(v___x_4504_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4505_);
v___x_4507_ = v___x_4455_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
v_a_4510_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4452_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4452_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object* v_declName_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object* v_as_4523_, size_t v_i_4524_, size_t v_stop_4525_, lean_object* v_b_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_usize_dec_eq(v_i_4524_, v_stop_4525_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = lean_array_uget_borrowed(v_as_4523_, v_i_4524_);
lean_inc(v___x_4531_);
v___x_4532_ = l_Lean_Elab_Command_elabCommand(v___x_4531_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; size_t v___x_4534_; size_t v___x_4535_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = ((size_t)1ULL);
v___x_4535_ = lean_usize_add(v_i_4524_, v___x_4534_);
v_i_4524_ = v___x_4535_;
v_b_4526_ = v_a_4533_;
goto _start;
}
else
{
return v___x_4532_;
}
}
else
{
lean_object* v___x_4537_; 
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_b_4526_);
return v___x_4537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object* v_as_4538_, lean_object* v_i_4539_, lean_object* v_stop_4540_, lean_object* v_b_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
size_t v_i_boxed_4545_; size_t v_stop_boxed_4546_; lean_object* v_res_4547_; 
v_i_boxed_4545_ = lean_unbox_usize(v_i_4539_);
lean_dec(v_i_4539_);
v_stop_boxed_4546_ = lean_unbox_usize(v_stop_4540_);
lean_dec(v_stop_4540_);
v_res_4547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_as_4538_, v_i_boxed_4545_, v_stop_boxed_4546_, v_b_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec_ref(v_as_4538_);
return v_res_4547_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10));
v___x_4576_ = l_String_toRawSubstring_x27(v___x_4575_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object* v___x_4580_, lean_object* v_declName_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v_a_4589_; lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4580_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4687_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4687_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4687_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___y_4654_; lean_object* v___x_4655_; 
lean_inc(v_declName_4581_);
v___x_4655_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___y_4657_; lean_object* v___x_4658_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
lean_inc(v_a_4617_);
v___y_4657_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed), 10, 3);
lean_closure_set(v___y_4657_, 0, v_a_4656_);
lean_closure_set(v___y_4657_, 1, v_a_4617_);
lean_closure_set(v___y_4657_, 2, v_declName_4581_);
v___x_4658_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_4657_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref_known(v___x_4658_, 1);
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = lean_array_get_size(v_a_4659_);
v___x_4662_ = lean_nat_dec_lt(v___x_4660_, v___x_4661_);
if (v___x_4662_ == 0)
{
lean_dec(v_a_4659_);
goto v___jp_4621_;
}
else
{
lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4663_ = lean_box(0);
v___x_4664_ = lean_nat_dec_le(v___x_4661_, v___x_4661_);
if (v___x_4664_ == 0)
{
if (v___x_4662_ == 0)
{
lean_dec(v_a_4659_);
goto v___jp_4621_;
}
else
{
size_t v___x_4665_; size_t v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = ((size_t)0ULL);
v___x_4666_ = lean_usize_of_nat(v___x_4661_);
v___x_4667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4659_, v___x_4665_, v___x_4666_, v___x_4663_, v___y_4582_, v___y_4583_);
lean_dec(v_a_4659_);
v___y_4654_ = v___x_4667_;
goto v___jp_4653_;
}
}
else
{
size_t v___x_4668_; size_t v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = ((size_t)0ULL);
v___x_4669_ = lean_usize_of_nat(v___x_4661_);
v___x_4670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4659_, v___x_4668_, v___x_4669_, v___x_4663_, v___y_4582_, v___y_4583_);
lean_dec(v_a_4659_);
v___y_4654_ = v___x_4670_;
goto v___jp_4653_;
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_del_object(v___x_4619_);
lean_dec(v_a_4617_);
lean_dec_ref(v___y_4582_);
v_a_4671_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4658_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4658_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_del_object(v___x_4619_);
lean_dec(v_a_4617_);
lean_dec_ref(v___y_4582_);
lean_dec(v_declName_4581_);
v_a_4679_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4655_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4655_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
v___jp_4621_:
{
uint8_t v_usePartial_4622_; 
v_usePartial_4622_ = lean_ctor_get_uint8(v_a_4617_, sizeof(void*)*3);
if (v_usePartial_4622_ == 0)
{
lean_object* v_instName_4623_; lean_object* v___x_4624_; 
lean_del_object(v___x_4619_);
v_instName_4623_ = lean_ctor_get(v_a_4617_, 0);
lean_inc(v_instName_4623_);
lean_dec(v_a_4617_);
v___x_4624_ = l_Lean_Elab_Command_getRef___redArg(v___y_4582_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4582_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v_quotContext_x3f_4628_; lean_object* v___x_4629_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v_quotContext_x3f_4628_ = lean_ctor_get(v___y_4582_, 5);
v___x_4629_ = l_Lean_SourceInfo_fromRef(v_a_4625_, v_usePartial_4622_);
lean_dec(v_a_4625_);
if (lean_obj_tag(v_quotContext_x3f_4628_) == 0)
{
lean_object* v___x_4630_; lean_object* v_a_4631_; 
v___x_4630_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4583_);
v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref(v___x_4630_);
v___y_4586_ = v_instName_4623_;
v___y_4587_ = v_a_4627_;
v___y_4588_ = v___x_4629_;
v_a_4589_ = v_a_4631_;
goto v___jp_4585_;
}
else
{
lean_object* v_val_4632_; 
v_val_4632_ = lean_ctor_get(v_quotContext_x3f_4628_, 0);
lean_inc(v_val_4632_);
v___y_4586_ = v_instName_4623_;
v___y_4587_ = v_a_4627_;
v___y_4588_ = v___x_4629_;
v_a_4589_ = v_val_4632_;
goto v___jp_4585_;
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_dec(v_a_4625_);
lean_dec(v_instName_4623_);
lean_dec_ref(v___y_4582_);
v_a_4633_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4626_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4626_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec(v_instName_4623_);
lean_dec_ref(v___y_4582_);
v_a_4641_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4624_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4624_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
lean_dec(v_a_4617_);
lean_dec_ref(v___y_4582_);
v___x_4649_ = lean_box(0);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v___x_4649_);
v___x_4651_ = v___x_4619_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
v___jp_4653_:
{
if (lean_obj_tag(v___y_4654_) == 0)
{
lean_dec_ref_known(v___y_4654_, 1);
goto v___jp_4621_;
}
else
{
lean_del_object(v___x_4619_);
lean_dec(v_a_4617_);
lean_dec_ref(v___y_4582_);
return v___y_4654_;
}
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_dec_ref(v___y_4582_);
lean_dec(v_declName_4581_);
v_a_4688_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4616_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4616_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
v___jp_4585_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0));
v___x_4591_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1));
lean_inc_n(v___y_4588_, 10);
v___x_4592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___y_4588_);
lean_ctor_set(v___x_4592_, 1, v___x_4590_);
v___x_4593_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2));
v___x_4594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4594_, 0, v___y_4588_);
lean_ctor_set(v___x_4594_, 1, v___x_4593_);
v___x_4595_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_4596_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4));
v___x_4597_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6));
v___x_4598_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_4599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4599_, 0, v___y_4588_);
lean_ctor_set(v___x_4599_, 1, v___x_4595_);
lean_ctor_set(v___x_4599_, 2, v___x_4598_);
lean_inc_ref(v___x_4599_);
v___x_4600_ = l_Lean_Syntax_node1(v___y_4588_, v___x_4597_, v___x_4599_);
v___x_4601_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9));
v___x_4602_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11);
v___x_4603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12));
v___x_4604_ = l_Lean_addMacroScope(v_a_4589_, v___x_4603_, v___y_4587_);
v___x_4605_ = lean_box(0);
v___x_4606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4606_, 0, v___y_4588_);
lean_ctor_set(v___x_4606_, 1, v___x_4602_);
lean_ctor_set(v___x_4606_, 2, v___x_4604_);
lean_ctor_set(v___x_4606_, 3, v___x_4605_);
v___x_4607_ = l_Lean_Syntax_node2(v___y_4588_, v___x_4601_, v___x_4606_, v___x_4599_);
v___x_4608_ = l_Lean_Syntax_node2(v___y_4588_, v___x_4596_, v___x_4600_, v___x_4607_);
v___x_4609_ = l_Lean_Syntax_node1(v___y_4588_, v___x_4595_, v___x_4608_);
v___x_4610_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13));
v___x_4611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___y_4588_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = l_Lean_mkIdent(v___y_4586_);
v___x_4613_ = l_Lean_Syntax_node1(v___y_4588_, v___x_4595_, v___x_4612_);
v___x_4614_ = l_Lean_Syntax_node5(v___y_4588_, v___x_4591_, v___x_4592_, v___x_4594_, v___x_4609_, v___x_4611_, v___x_4613_);
v___x_4615_ = l_Lean_Elab_Command_elabCommand(v___x_4614_, v___y_4582_, v___y_4583_);
lean_dec_ref(v___y_4582_);
return v___x_4615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object* v___x_4696_, lean_object* v_declName_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(v___x_4696_, v_declName_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object* v_declName_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; 
v___x_4706_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_4707_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_4708_ = 1;
v___x_4709_ = lean_box(v___x_4708_);
lean_inc_n(v_declName_4702_, 2);
v___x_4710_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkContext___boxed), 11, 4);
lean_closure_set(v___x_4710_, 0, v___x_4706_);
lean_closure_set(v___x_4710_, 1, v___x_4707_);
lean_closure_set(v___x_4710_, 2, v_declName_4702_);
lean_closure_set(v___x_4710_, 3, v___x_4709_);
v___f_4711_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed), 5, 2);
lean_closure_set(v___f_4711_, 0, v___x_4710_);
lean_closure_set(v___f_4711_, 1, v_declName_4702_);
v___x_4712_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4702_, v___f_4711_, v_a_4703_, v_a_4704_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object* v_declName_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_declName_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_4718_, lean_object* v_constName_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4719_, v___y_4720_, v___y_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4724_, lean_object* v_constName_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(v_00_u03b1_4724_, v_constName_4725_, v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4730_, lean_object* v_ref_4731_, lean_object* v_constName_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4731_, v_constName_4732_, v___y_4733_, v___y_4734_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4737_, lean_object* v_ref_4738_, lean_object* v_constName_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_4737_, v_ref_4738_, v_constName_4739_, v___y_4740_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v_ref_4738_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4744_, lean_object* v_ref_4745_, lean_object* v_msg_4746_, lean_object* v_declHint_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4745_, v_msg_4746_, v_declHint_4747_, v___y_4748_, v___y_4749_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4752_, lean_object* v_ref_4753_, lean_object* v_msg_4754_, lean_object* v_declHint_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4752_, v_ref_4753_, v_msg_4754_, v_declHint_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v_ref_4753_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_4760_, lean_object* v_declHint_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4760_, v_declHint_4761_, v___y_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_4766_, lean_object* v_declHint_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_4766_, v_declHint_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_4772_, lean_object* v_ref_4773_, lean_object* v_msg_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4773_, v_msg_4774_, v___y_4775_, v___y_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4779_, lean_object* v_ref_4780_, lean_object* v_msg_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_4779_, v_ref_4780_, v_msg_4781_, v___y_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v_ref_4780_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4786_, v___y_4788_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_4791_, v___y_4792_, v___y_4793_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_4796_, lean_object* v_msg_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4797_, v___y_4798_, v___y_4799_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4802_, lean_object* v_msg_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4802_, v_msg_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object* v_msgData_4808_, lean_object* v_macroStack_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4808_, v_macroStack_4809_, v___y_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object* v_msgData_4814_, lean_object* v_macroStack_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(v_msgData_4814_, v_macroStack_4815_, v___y_4816_, v___y_4817_);
lean_dec(v___y_4817_);
lean_dec_ref(v___y_4816_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; lean_object* v_env_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4823_ = lean_st_ref_get(v___y_4821_);
v_env_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4823_);
v___x_4825_ = l_Lean_isInductiveCore(v_env_4824_, v_declName_4820_);
v___x_4826_ = lean_box(v___x_4825_);
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4828_, v___y_4829_);
lean_dec(v___y_4829_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object* v_declName_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4832_, v___y_4834_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(v_declName_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t v_____do__lift_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4846_ = lean_bool_not(v_____do__lift_4842_);
v___x_4847_ = lean_box(v___x_4846_);
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
uint8_t v_____do__lift_1670__boxed_4853_; lean_object* v_res_4854_; 
v_____do__lift_1670__boxed_4853_ = lean_unbox(v_____do__lift_4849_);
v_res_4854_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v_____do__lift_1670__boxed_4853_, v___y_4850_, v___y_4851_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object* v_as_4855_, size_t v_i_4856_, size_t v_stop_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
uint8_t v___x_4861_; 
v___x_4861_ = lean_usize_dec_eq(v_i_4856_, v_stop_4857_);
if (v___x_4861_ == 0)
{
uint8_t v___x_4862_; uint8_t v_a_4864_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4862_ = 1;
v___x_4870_ = lean_array_uget_borrowed(v_as_4855_, v_i_4856_);
lean_inc(v___x_4870_);
v___x_4871_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v___x_4870_, v___y_4859_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; uint8_t v___x_4873_; uint8_t v___x_4874_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4871_, 1);
v___x_4873_ = lean_unbox(v_a_4872_);
lean_dec(v_a_4872_);
v___x_4874_ = lean_bool_not(v___x_4873_);
v_a_4864_ = v___x_4874_;
goto v___jp_4863_;
}
else
{
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4875_; uint8_t v___x_4876_; 
v_a_4875_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4871_, 1);
v___x_4876_ = lean_unbox(v_a_4875_);
lean_dec(v_a_4875_);
v_a_4864_ = v___x_4876_;
goto v___jp_4863_;
}
else
{
return v___x_4871_;
}
}
v___jp_4863_:
{
if (v_a_4864_ == 0)
{
size_t v___x_4865_; size_t v___x_4866_; 
v___x_4865_ = ((size_t)1ULL);
v___x_4866_ = lean_usize_add(v_i_4856_, v___x_4865_);
v_i_4856_ = v___x_4866_;
goto _start;
}
else
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = lean_box(v___x_4862_);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
return v___x_4869_;
}
}
}
else
{
uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = 0;
v___x_4878_ = lean_box(v___x_4877_);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object* v_as_4880_, lean_object* v_i_4881_, lean_object* v_stop_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
size_t v_i_boxed_4886_; size_t v_stop_boxed_4887_; lean_object* v_res_4888_; 
v_i_boxed_4886_ = lean_unbox_usize(v_i_4881_);
lean_dec(v_i_4881_);
v_stop_boxed_4887_ = lean_unbox_usize(v_stop_4882_);
lean_dec(v_stop_4882_);
v_res_4888_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_as_4880_, v_i_boxed_4886_, v_stop_boxed_4887_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec_ref(v_as_4880_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object* v_as_4889_, size_t v_sz_4890_, size_t v_i_4891_, lean_object* v_b_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
uint8_t v___x_4896_; 
v___x_4896_ = lean_usize_dec_lt(v_i_4891_, v_sz_4890_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; 
v___x_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4897_, 0, v_b_4892_);
return v___x_4897_;
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4899_; 
v_a_4898_ = lean_array_uget_borrowed(v_as_4889_, v_i_4891_);
lean_inc(v_a_4898_);
v___x_4899_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_a_4898_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v___x_4900_; size_t v___x_4901_; size_t v___x_4902_; 
lean_dec_ref_known(v___x_4899_, 1);
v___x_4900_ = lean_box(0);
v___x_4901_ = ((size_t)1ULL);
v___x_4902_ = lean_usize_add(v_i_4891_, v___x_4901_);
v_i_4891_ = v___x_4902_;
v_b_4892_ = v___x_4900_;
goto _start;
}
else
{
return v___x_4899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object* v_as_4904_, lean_object* v_sz_4905_, lean_object* v_i_4906_, lean_object* v_b_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
size_t v_sz_boxed_4911_; size_t v_i_boxed_4912_; lean_object* v_res_4913_; 
v_sz_boxed_4911_ = lean_unbox_usize(v_sz_4905_);
lean_dec(v_sz_4905_);
v_i_boxed_4912_ = lean_unbox_usize(v_i_4906_);
lean_dec(v_i_4906_);
v_res_4913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_as_4904_, v_sz_boxed_4911_, v_i_boxed_4912_, v_b_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec_ref(v_as_4904_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object* v_declNames_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
uint8_t v_a_4919_; lean_object* v___y_4944_; lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = lean_array_get_size(v_declNames_4914_);
v___x_4949_ = lean_nat_dec_lt(v___x_4947_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; 
v___x_4950_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4949_, v_a_4915_, v_a_4916_);
v___y_4944_ = v___x_4950_;
goto v___jp_4943_;
}
else
{
if (v___x_4949_ == 0)
{
uint8_t v___x_4951_; 
v___x_4951_ = lean_bool_not(v___x_4949_);
v_a_4919_ = v___x_4951_;
goto v___jp_4918_;
}
else
{
size_t v___x_4952_; size_t v___x_4953_; lean_object* v___x_4954_; 
v___x_4952_ = ((size_t)0ULL);
v___x_4953_ = lean_usize_of_nat(v___x_4948_);
v___x_4954_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_declNames_4914_, v___x_4952_, v___x_4953_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v___x_4956_ = lean_unbox(v_a_4955_);
lean_dec(v_a_4955_);
v___x_4957_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4956_, v_a_4915_, v_a_4916_);
v___y_4944_ = v___x_4957_;
goto v___jp_4943_;
}
else
{
v___y_4944_ = v___x_4954_;
goto v___jp_4943_;
}
}
}
v___jp_4918_:
{
if (v_a_4919_ == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = lean_box(v_a_4919_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
else
{
lean_object* v___x_4922_; size_t v_sz_4923_; size_t v___x_4924_; lean_object* v___x_4925_; 
v___x_4922_ = lean_box(0);
v_sz_4923_ = lean_array_size(v_declNames_4914_);
v___x_4924_ = ((size_t)0ULL);
v___x_4925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_declNames_4914_, v_sz_4923_, v___x_4924_, v___x_4922_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4933_; 
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4933_ == 0)
{
lean_object* v_unused_4934_; 
v_unused_4934_ = lean_ctor_get(v___x_4925_, 0);
lean_dec(v_unused_4934_);
v___x_4927_ = v___x_4925_;
v_isShared_4928_ = v_isSharedCheck_4933_;
goto v_resetjp_4926_;
}
else
{
lean_dec(v___x_4925_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4933_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4929_ = lean_box(v_a_4919_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v___x_4929_);
v___x_4931_ = v___x_4927_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4929_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
v_a_4935_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4925_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4925_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
v___jp_4943_:
{
if (lean_obj_tag(v___y_4944_) == 0)
{
lean_object* v_a_4945_; uint8_t v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___y_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___y_4944_, 1);
v___x_4946_ = lean_unbox(v_a_4945_);
lean_dec(v_a_4945_);
v_a_4919_ = v___x_4946_;
goto v___jp_4918_;
}
else
{
return v___y_4944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object* v_declNames_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(v_declNames_4958_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec_ref(v_declNames_4958_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_4999_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_5000_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5001_ = l_Lean_Elab_registerDerivingHandler(v___x_4999_, v___x_5000_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v___x_5002_; uint8_t v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
lean_dec_ref_known(v___x_5001_, 1);
v___x_5002_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_5003_ = 0;
v___x_5004_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5005_ = l_Lean_registerTraceClass(v___x_5002_, v___x_5003_, v___x_5004_);
return v___x_5005_;
}
else
{
return v___x_5001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
return v_res_5007_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
