// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 215, 55, 153, 7, 83, 44, 161)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(35, 209, 53, 49, 90, 19, 84, 123)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
static const lean_string_object l_Lean_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_mkCtorIdxName___closed__0 = (const lean_object*)&l_Lean_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCtorIdx_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCtorIdx_spec__10___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCtorIdx_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.mkCtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_Lean_mkCtorIdx___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__1;
static const lean_string_object l_Lean_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_mkCtorIdx___closed__2 = (const lean_object*)&l_Lean_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object* v_indName_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_82_ = l_Lean_Name_str___override(v_indName_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object* v_env_83_, lean_object* v_declName_84_){
_start:
{
if (lean_obj_tag(v_declName_84_) == 1)
{
lean_object* v_pre_85_; lean_object* v_str_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_pre_85_ = lean_ctor_get(v_declName_84_, 0);
lean_inc(v_pre_85_);
v_str_86_ = lean_ctor_get(v_declName_84_, 1);
lean_inc_ref(v_str_86_);
lean_dec_ref_known(v_declName_84_, 2);
v___x_87_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_88_ = lean_string_dec_eq(v_str_86_, v___x_87_);
lean_dec_ref(v_str_86_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v_pre_85_);
lean_dec_ref(v_env_83_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_isInductiveCore_x3f(v_env_83_, v_pre_85_);
return v___x_90_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v_declName_84_);
lean_dec_ref(v_env_83_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object* v_declName_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_st_ref_get(v_a_93_);
v_env_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_env_96_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_isCtorIdxCore_x3f(v_env_96_, v_declName_92_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_99_, v_a_100_);
lean_dec(v_a_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object* v_declName_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_103_, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object* v_declName_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_isCtorIdx_x3f(v_declName_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_117_, lean_object* v_opt_118_){
_start:
{
lean_object* v_name_119_; lean_object* v_defValue_120_; lean_object* v_map_121_; lean_object* v___x_122_; 
v_name_119_ = lean_ctor_get(v_opt_118_, 0);
v_defValue_120_ = lean_ctor_get(v_opt_118_, 1);
v_map_121_ = lean_ctor_get(v_opts_117_, 0);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_121_, v_name_119_);
if (lean_obj_tag(v___x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = lean_unbox(v_defValue_120_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; 
v_val_124_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v___x_122_, 1);
if (lean_obj_tag(v_val_124_) == 1)
{
uint8_t v_v_125_; 
v_v_125_ = lean_ctor_get_uint8(v_val_124_, 0);
lean_dec_ref_known(v_val_124_, 0);
return v_v_125_;
}
else
{
uint8_t v___x_126_; 
lean_dec(v_val_124_);
v___x_126_ = lean_unbox(v_defValue_120_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_127_, v_opt_128_);
lean_dec_ref(v_opt_128_);
lean_dec_ref(v_opts_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_131_, uint8_t v_skipRealize_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_env_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = lean_st_ref_get(v___y_133_);
v_env_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_env_136_);
lean_dec(v___x_135_);
v___x_137_ = l_Lean_Environment_contains(v_env_136_, v_constName_131_, v_skipRealize_132_);
v___x_138_ = lean_box(v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_140_, lean_object* v_skipRealize_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
uint8_t v_skipRealize_boxed_144_; lean_object* v_res_145_; 
v_skipRealize_boxed_144_ = lean_unbox(v_skipRealize_141_);
v_res_145_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_140_, v_skipRealize_boxed_144_, v___y_142_);
lean_dec(v___y_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_146_, uint8_t v_skipRealize_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_146_, v_skipRealize_147_, v___y_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_154_, lean_object* v_skipRealize_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
uint8_t v_skipRealize_boxed_161_; lean_object* v_res_162_; 
v_skipRealize_boxed_161_ = lean_unbox(v_skipRealize_155_);
v_res_162_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_154_, v_skipRealize_boxed_161_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_163_, lean_object* v_b_164_, lean_object* v_c_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_171_ = lean_apply_7(v_k_163_, v_b_164_, v_c_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_172_, lean_object* v_b_173_, lean_object* v_c_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(v_k_172_, v_b_173_, v_c_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_181_, lean_object* v_maxFVars_x3f_182_, lean_object* v_k_183_, uint8_t v_cleanupAnnotations_184_, uint8_t v_whnfType_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___f_191_; lean_object* v___x_192_; 
v___f_191_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_191_, 0, v_k_183_);
v___x_192_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_181_, v_maxFVars_x3f_182_, v___f_191_, v_cleanupAnnotations_184_, v_whnfType_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_192_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_192_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_209_, lean_object* v_maxFVars_x3f_210_, lean_object* v_k_211_, lean_object* v_cleanupAnnotations_212_, lean_object* v_whnfType_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_219_; uint8_t v_whnfType_boxed_220_; lean_object* v_res_221_; 
v_cleanupAnnotations_boxed_219_ = lean_unbox(v_cleanupAnnotations_212_);
v_whnfType_boxed_220_ = lean_unbox(v_whnfType_213_);
v_res_221_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_209_, v_maxFVars_x3f_210_, v_k_211_, v_cleanupAnnotations_boxed_219_, v_whnfType_boxed_220_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_222_, lean_object* v_type_223_, lean_object* v_maxFVars_x3f_224_, lean_object* v_k_225_, uint8_t v_cleanupAnnotations_226_, uint8_t v_whnfType_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_223_, v_maxFVars_x3f_224_, v_k_225_, v_cleanupAnnotations_226_, v_whnfType_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_234_, lean_object* v_type_235_, lean_object* v_maxFVars_x3f_236_, lean_object* v_k_237_, lean_object* v_cleanupAnnotations_238_, lean_object* v_whnfType_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_245_; uint8_t v_whnfType_boxed_246_; lean_object* v_res_247_; 
v_cleanupAnnotations_boxed_245_ = lean_unbox(v_cleanupAnnotations_238_);
v_whnfType_boxed_246_ = lean_unbox(v_whnfType_239_);
v_res_247_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_234_, v_type_235_, v_maxFVars_x3f_236_, v_k_237_, v_cleanupAnnotations_boxed_245_, v_whnfType_boxed_246_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_248_, lean_object* v_levelParams_249_, lean_object* v_type_250_, lean_object* v_value_251_, lean_object* v_hints_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; uint8_t v___y_257_; uint8_t v___y_264_; lean_object* v_env_267_; uint8_t v___x_268_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_env_267_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref_n(v_env_267_, 2);
lean_dec(v___x_255_);
v___x_268_ = l_Lean_Environment_hasUnsafe(v_env_267_, v_type_250_);
if (v___x_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_Environment_hasUnsafe(v_env_267_, v_value_251_);
v___y_264_ = v___x_269_;
goto v___jp_263_;
}
else
{
lean_dec_ref(v_env_267_);
v___y_264_ = v___x_268_;
goto v___jp_263_;
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
lean_inc(v_name_248_);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v_name_248_);
lean_ctor_set(v___x_258_, 1, v_levelParams_249_);
lean_ctor_set(v___x_258_, 2, v_type_250_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v_name_248_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_261_, 0, v___x_258_);
lean_ctor_set(v___x_261_, 1, v_value_251_);
lean_ctor_set(v___x_261_, 2, v_hints_252_);
lean_ctor_set(v___x_261_, 3, v___x_260_);
lean_ctor_set_uint8(v___x_261_, sizeof(void*)*4, v___y_257_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
v___jp_263_:
{
if (v___y_264_ == 0)
{
uint8_t v___x_265_; 
v___x_265_ = 1;
v___y_257_ = v___x_265_;
goto v___jp_256_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = 0;
v___y_257_ = v___x_266_;
goto v___jp_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_270_, lean_object* v_levelParams_271_, lean_object* v_type_272_, lean_object* v_value_273_, lean_object* v_hints_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_270_, v_levelParams_271_, v_type_272_, v_value_273_, v_hints_274_, v___y_275_);
lean_dec(v___y_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_278_, lean_object* v_levelParams_279_, lean_object* v_type_280_, lean_object* v_value_281_, lean_object* v_hints_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_278_, v_levelParams_279_, v_type_280_, v_value_281_, v_hints_282_, v___y_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_289_, lean_object* v_levelParams_290_, lean_object* v_type_291_, lean_object* v_value_292_, lean_object* v_hints_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_289_, v_levelParams_290_, v_type_291_, v_value_292_, v_hints_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__10(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_12120__overap_308_; lean_object* v___x_309_; 
v___f_307_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__10___closed__0));
v___x_12120__overap_308_ = lean_panic_fn_borrowed(v___f_307_, v_msg_301_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_309_ = lean_apply_5(v___x_12120__overap_308_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_panic___at___00Lean_mkCtorIdx_spec__10(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0(lean_object* v___y_317_, uint8_t v_isExporting_318_, lean_object* v___x_319_, lean_object* v___y_320_, lean_object* v___x_321_, lean_object* v_a_x3f_322_){
_start:
{
lean_object* v___x_324_; lean_object* v_env_325_; lean_object* v_nextMacroScope_326_; lean_object* v_ngen_327_; lean_object* v_auxDeclNGen_328_; lean_object* v_traceState_329_; lean_object* v_messages_330_; lean_object* v_infoState_331_; lean_object* v_snapshotTasks_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_357_; 
v___x_324_ = lean_st_ref_take(v___y_317_);
v_env_325_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_326_ = lean_ctor_get(v___x_324_, 1);
v_ngen_327_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_328_ = lean_ctor_get(v___x_324_, 3);
v_traceState_329_ = lean_ctor_get(v___x_324_, 4);
v_messages_330_ = lean_ctor_get(v___x_324_, 6);
v_infoState_331_ = lean_ctor_get(v___x_324_, 7);
v_snapshotTasks_332_ = lean_ctor_get(v___x_324_, 8);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v___x_324_, 5);
lean_dec(v_unused_358_);
v___x_334_ = v___x_324_;
v_isShared_335_ = v_isSharedCheck_357_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snapshotTasks_332_);
lean_inc(v_infoState_331_);
lean_inc(v_messages_330_);
lean_inc(v_traceState_329_);
lean_inc(v_auxDeclNGen_328_);
lean_inc(v_ngen_327_);
lean_inc(v_nextMacroScope_326_);
lean_inc(v_env_325_);
lean_dec(v___x_324_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_357_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = l_Lean_Environment_setExporting(v_env_325_, v_isExporting_318_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 5, v___x_319_);
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_nextMacroScope_326_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_ngen_327_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_auxDeclNGen_328_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_traceState_329_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_messages_330_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_infoState_331_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v_snapshotTasks_332_);
v___x_338_ = v_reuseFailAlloc_356_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_mctx_341_; lean_object* v_zetaDeltaFVarIds_342_; lean_object* v_postponed_343_; lean_object* v_diag_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_354_; 
v___x_339_ = lean_st_ref_put(v___y_317_, v___x_338_);
v___x_340_ = lean_st_ref_take(v___y_320_);
v_mctx_341_ = lean_ctor_get(v___x_340_, 0);
v_zetaDeltaFVarIds_342_ = lean_ctor_get(v___x_340_, 2);
v_postponed_343_ = lean_ctor_get(v___x_340_, 3);
v_diag_344_ = lean_ctor_get(v___x_340_, 4);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_340_, 1);
lean_dec(v_unused_355_);
v___x_346_ = v___x_340_;
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_diag_344_);
lean_inc(v_postponed_343_);
lean_inc(v_zetaDeltaFVarIds_342_);
lean_inc(v_mctx_341_);
lean_dec(v___x_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_321_);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_mctx_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_zetaDeltaFVarIds_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_postponed_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_diag_344_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_st_ref_put(v___y_320_, v___x_349_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0___boxed(lean_object* v___y_359_, lean_object* v_isExporting_360_, lean_object* v___x_361_, lean_object* v___y_362_, lean_object* v___x_363_, lean_object* v_a_x3f_364_, lean_object* v___y_365_){
_start:
{
uint8_t v_isExporting_boxed_366_; lean_object* v_res_367_; 
v_isExporting_boxed_366_ = lean_unbox(v_isExporting_360_);
v_res_367_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0(v___y_359_, v_isExporting_boxed_366_, v___x_361_, v___y_362_, v___x_363_, v_a_x3f_364_);
lean_dec(v_a_x3f_364_);
lean_dec(v___y_362_);
lean_dec(v___y_359_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_368_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__0);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__1);
v___x_374_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
lean_ctor_set(v___x_374_, 3, v___x_373_);
lean_ctor_set(v___x_374_, 4, v___x_373_);
lean_ctor_set(v___x_374_, 5, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(lean_object* v_x_375_, uint8_t v_isExporting_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; lean_object* v_env_383_; lean_object* v___x_384_; uint8_t v_isModule_385_; 
v___x_382_ = lean_st_ref_get(v___y_380_);
v_env_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_env_383_);
lean_dec(v___x_382_);
v___x_384_ = l_Lean_Environment_header(v_env_383_);
v_isModule_385_ = lean_ctor_get_uint8(v___x_384_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_384_);
if (v_isModule_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v_env_383_);
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
v___x_386_ = lean_apply_5(v_x_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, lean_box(0));
return v___x_386_;
}
else
{
uint8_t v_isExporting_387_; 
v_isExporting_387_ = lean_ctor_get_uint8(v_env_383_, sizeof(void*)*8);
lean_dec_ref(v_env_383_);
if (v_isExporting_376_ == 0)
{
if (v_isExporting_387_ == 0)
{
lean_object* v___x_453_; 
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
v___x_453_ = lean_apply_5(v_x_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, lean_box(0));
return v___x_453_;
}
else
{
goto v___jp_388_;
}
}
else
{
if (v_isExporting_387_ == 0)
{
goto v___jp_388_;
}
else
{
lean_object* v___x_454_; 
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
v___x_454_ = lean_apply_5(v_x_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, lean_box(0));
return v___x_454_;
}
}
v___jp_388_:
{
lean_object* v___x_389_; lean_object* v_env_390_; lean_object* v_nextMacroScope_391_; lean_object* v_ngen_392_; lean_object* v_auxDeclNGen_393_; lean_object* v_traceState_394_; lean_object* v_messages_395_; lean_object* v_infoState_396_; lean_object* v_snapshotTasks_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_451_; 
v___x_389_ = lean_st_ref_take(v___y_380_);
v_env_390_ = lean_ctor_get(v___x_389_, 0);
v_nextMacroScope_391_ = lean_ctor_get(v___x_389_, 1);
v_ngen_392_ = lean_ctor_get(v___x_389_, 2);
v_auxDeclNGen_393_ = lean_ctor_get(v___x_389_, 3);
v_traceState_394_ = lean_ctor_get(v___x_389_, 4);
v_messages_395_ = lean_ctor_get(v___x_389_, 6);
v_infoState_396_ = lean_ctor_get(v___x_389_, 7);
v_snapshotTasks_397_ = lean_ctor_get(v___x_389_, 8);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_389_, 5);
lean_dec(v_unused_452_);
v___x_399_ = v___x_389_;
v_isShared_400_ = v_isSharedCheck_451_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snapshotTasks_397_);
lean_inc(v_infoState_396_);
lean_inc(v_messages_395_);
lean_inc(v_traceState_394_);
lean_inc(v_auxDeclNGen_393_);
lean_inc(v_ngen_392_);
lean_inc(v_nextMacroScope_391_);
lean_inc(v_env_390_);
lean_dec(v___x_389_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_451_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_Environment_setExporting(v_env_390_, v_isExporting_376_);
v___x_402_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 5, v___x_402_);
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_nextMacroScope_391_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_ngen_392_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_auxDeclNGen_393_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_traceState_394_);
lean_ctor_set(v_reuseFailAlloc_450_, 5, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_450_, 6, v_messages_395_);
lean_ctor_set(v_reuseFailAlloc_450_, 7, v_infoState_396_);
lean_ctor_set(v_reuseFailAlloc_450_, 8, v_snapshotTasks_397_);
v___x_404_ = v_reuseFailAlloc_450_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_mctx_407_; lean_object* v_zetaDeltaFVarIds_408_; lean_object* v_postponed_409_; lean_object* v_diag_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_448_; 
v___x_405_ = lean_st_ref_put(v___y_380_, v___x_404_);
v___x_406_ = lean_st_ref_take(v___y_378_);
v_mctx_407_ = lean_ctor_get(v___x_406_, 0);
v_zetaDeltaFVarIds_408_ = lean_ctor_get(v___x_406_, 2);
v_postponed_409_ = lean_ctor_get(v___x_406_, 3);
v_diag_410_ = lean_ctor_get(v___x_406_, 4);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_406_, 1);
lean_dec(v_unused_449_);
v___x_412_ = v___x_406_;
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_diag_410_);
lean_inc(v_postponed_409_);
lean_inc(v_zetaDeltaFVarIds_408_);
lean_inc(v_mctx_407_);
lean_dec(v___x_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_mctx_407_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_zetaDeltaFVarIds_408_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_postponed_409_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_diag_410_);
v___x_416_ = v_reuseFailAlloc_447_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v_r_418_; 
v___x_417_ = lean_st_ref_put(v___y_378_, v___x_416_);
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
v_r_418_ = lean_apply_5(v_x_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, lean_box(0));
if (lean_obj_tag(v_r_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_435_; 
v_a_419_ = lean_ctor_get(v_r_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_r_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_421_ = v_r_418_;
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v_r_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
lean_inc(v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 1);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_434_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
v___x_425_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0(v___y_380_, v_isExporting_387_, v___x_402_, v___y_378_, v___x_414_, v___x_424_);
lean_dec_ref(v___x_424_);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_425_, 0);
lean_dec(v_unused_433_);
v___x_427_ = v___x_425_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_dec(v___x_425_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_a_419_);
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_419_);
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
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_436_ = lean_ctor_get(v_r_418_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v_r_418_, 1);
v___x_437_ = lean_box(0);
v___x_438_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___lam__0(v___y_380_, v_isExporting_387_, v___x_402_, v___y_378_, v___x_414_, v___x_437_);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_438_, 0);
lean_dec(v_unused_446_);
v___x_440_ = v___x_438_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___x_438_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
lean_ctor_set(v___x_440_, 0, v_a_436_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_436_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___boxed(lean_object* v_x_455_, lean_object* v_isExporting_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v_isExporting_boxed_462_; lean_object* v_res_463_; 
v_isExporting_boxed_462_ = lean_unbox(v_isExporting_456_);
v_res_463_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(v_x_455_, v_isExporting_boxed_462_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11(lean_object* v_00_u03b1_464_, lean_object* v_x_465_, uint8_t v_isExporting_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(v_x_465_, v_isExporting_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_00_u03b1_473_, lean_object* v_x_474_, lean_object* v_isExporting_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v_isExporting_boxed_481_; lean_object* v_res_482_; 
v_isExporting_boxed_481_ = lean_unbox(v_isExporting_475_);
v_res_482_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11(v_00_u03b1_473_, v_x_474_, v_isExporting_boxed_481_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_483_, uint8_t v___x_484_, uint8_t v___x_485_, uint8_t v___x_486_, lean_object* v_ys_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = l_Lean_mkRawNatLit(v_cidx_483_);
v___x_495_ = l_Lean_Meta_mkLambdaFVars(v_ys_487_, v___x_494_, v___x_484_, v___x_485_, v___x_484_, v___x_485_, v___x_486_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, lean_object* v_ys_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_19141__boxed_507_; uint8_t v___x_19142__boxed_508_; uint8_t v___x_19143__boxed_509_; lean_object* v_res_510_; 
v___x_19141__boxed_507_ = lean_unbox(v___x_497_);
v___x_19142__boxed_508_ = lean_unbox(v___x_498_);
v___x_19143__boxed_509_ = lean_unbox(v___x_499_);
v_res_510_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_496_, v___x_19141__boxed_507_, v___x_19142__boxed_508_, v___x_19143__boxed_509_, v_ys_500_, v_x_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec_ref(v_x_501_);
lean_dec_ref(v_ys_500_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_env_518_; lean_object* v___x_519_; lean_object* v_mctx_520_; lean_object* v_lctx_521_; lean_object* v_options_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_517_ = lean_st_ref_get(v___y_515_);
v_env_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_env_518_);
lean_dec(v___x_517_);
v___x_519_ = lean_st_ref_get(v___y_513_);
v_mctx_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_mctx_520_);
lean_dec(v___x_519_);
v_lctx_521_ = lean_ctor_get(v___y_512_, 2);
v_options_522_ = lean_ctor_get(v___y_514_, 1);
lean_inc_ref(v_options_522_);
lean_inc_ref(v_lctx_521_);
v___x_523_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_523_, 0, v_env_518_);
lean_ctor_set(v___x_523_, 1, v_mctx_520_);
lean_ctor_set(v___x_523_, 2, v_lctx_521_);
lean_ctor_set(v___x_523_, 3, v_options_522_);
v___x_524_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_msgData_511_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_ref_539_; lean_object* v___x_540_; lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_ref_539_ = lean_ctor_get(v___y_536_, 4);
v___x_540_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_549_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
lean_inc(v_ref_539_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_ref_539_);
lean_ctor_set(v___x_545_, 1, v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 1);
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_556_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_instMonadEIO(lean_box(0));
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_toApplicative_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_631_; 
v___x_568_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_569_ = l_StateRefT_x27_instMonad___redArg(v___x_568_);
v_toApplicative_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v___x_569_, 1);
lean_dec(v_unused_632_);
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_631_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_toApplicative_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_631_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_toFunctor_574_; lean_object* v_toSeq_575_; lean_object* v_toSeqLeft_576_; lean_object* v_toSeqRight_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_629_; 
v_toFunctor_574_ = lean_ctor_get(v_toApplicative_570_, 0);
v_toSeq_575_ = lean_ctor_get(v_toApplicative_570_, 2);
v_toSeqLeft_576_ = lean_ctor_get(v_toApplicative_570_, 3);
v_toSeqRight_577_ = lean_ctor_get(v_toApplicative_570_, 4);
v_isSharedCheck_629_ = !lean_is_exclusive(v_toApplicative_570_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_toApplicative_570_, 1);
lean_dec(v_unused_630_);
v___x_579_ = v_toApplicative_570_;
v_isShared_580_ = v_isSharedCheck_629_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_toSeqRight_577_);
lean_inc(v_toSeqLeft_576_);
lean_inc(v_toSeq_575_);
lean_inc(v_toFunctor_574_);
lean_dec(v_toApplicative_570_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_629_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_590_; 
v___f_581_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_582_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_574_);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_583_, 0, v_toFunctor_574_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_584_, 0, v_toFunctor_574_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___f_583_);
lean_ctor_set(v___x_585_, 1, v___f_584_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toSeqRight_577_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeqLeft_576_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeq_575_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 4, v___f_586_);
lean_ctor_set(v___x_579_, 3, v___f_587_);
lean_ctor_set(v___x_579_, 2, v___f_588_);
lean_ctor_set(v___x_579_, 1, v___f_581_);
lean_ctor_set(v___x_579_, 0, v___x_585_);
v___x_590_ = v___x_579_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___f_581_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v___f_588_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v___f_587_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v___f_586_);
v___x_590_ = v_reuseFailAlloc_628_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___f_582_);
lean_ctor_set(v___x_572_, 0, v___x_590_);
v___x_592_ = v___x_572_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___f_582_);
v___x_592_ = v_reuseFailAlloc_627_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v_toApplicative_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_625_; 
v___x_593_ = l_StateRefT_x27_instMonad___redArg(v___x_592_);
v_toApplicative_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_593_, 1);
lean_dec(v_unused_626_);
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_625_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_toApplicative_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_625_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_toFunctor_598_; lean_object* v_toSeq_599_; lean_object* v_toSeqLeft_600_; lean_object* v_toSeqRight_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_623_; 
v_toFunctor_598_ = lean_ctor_get(v_toApplicative_594_, 0);
v_toSeq_599_ = lean_ctor_get(v_toApplicative_594_, 2);
v_toSeqLeft_600_ = lean_ctor_get(v_toApplicative_594_, 3);
v_toSeqRight_601_ = lean_ctor_get(v_toApplicative_594_, 4);
v_isSharedCheck_623_ = !lean_is_exclusive(v_toApplicative_594_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_toApplicative_594_, 1);
lean_dec(v_unused_624_);
v___x_603_ = v_toApplicative_594_;
v_isShared_604_ = v_isSharedCheck_623_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_toSeqRight_601_);
lean_inc(v_toSeqLeft_600_);
lean_inc(v_toSeq_599_);
lean_inc(v_toFunctor_598_);
lean_dec(v_toApplicative_594_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_623_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_614_; 
v___f_605_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_606_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_598_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_607_, 0, v_toFunctor_598_);
v___f_608_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_608_, 0, v_toFunctor_598_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___f_607_);
lean_ctor_set(v___x_609_, 1, v___f_608_);
v___f_610_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_610_, 0, v_toSeqRight_601_);
v___f_611_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_611_, 0, v_toSeqLeft_600_);
v___f_612_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_612_, 0, v_toSeq_599_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 4, v___f_610_);
lean_ctor_set(v___x_603_, 3, v___f_611_);
lean_ctor_set(v___x_603_, 2, v___f_612_);
lean_ctor_set(v___x_603_, 1, v___f_605_);
lean_ctor_set(v___x_603_, 0, v___x_609_);
v___x_614_ = v___x_603_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___f_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___f_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___f_610_);
v___x_614_ = v_reuseFailAlloc_622_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___f_606_);
lean_ctor_set(v___x_596_, 0, v___x_614_);
v___x_616_ = v___x_596_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___f_606_);
v___x_616_ = v_reuseFailAlloc_621_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_15499__overap_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v___x_618_ = l_instInhabitedOfMonad___redArg(v___x_616_, v___x_617_);
v___x_15499__overap_619_ = lean_panic_fn_borrowed(v___x_618_, v_msg_562_);
lean_dec(v___x_618_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
v___x_620_ = lean_apply_5(v___x_15499__overap_619_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
return v___x_620_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_650_ = lean_unsigned_to_nat(11u);
v___x_651_ = lean_unsigned_to_nat(122u);
v___x_652_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_653_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_654_ = l_mkPanicMessageWithDecl(v___x_653_, v___x_652_, v___x_651_, v___x_650_, v___x_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_669_; lean_object* v_env_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_st_ref_get(v___y_659_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v___x_671_ = 0;
lean_inc(v_constName_655_);
v___x_672_ = l_Lean_Environment_findAsync_x3f(v_env_670_, v_constName_655_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 1)
{
lean_object* v_val_673_; uint8_t v_kind_674_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_672_, 1);
v_kind_674_ = lean_ctor_get_uint8(v_val_673_, sizeof(void*)*3);
if (v_kind_674_ == 6)
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_673_);
if (lean_obj_tag(v___x_675_) == 6)
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_constName_655_);
v_val_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 0);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_val_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec_ref(v___x_675_);
v___x_684_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_685_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_684_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_694_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
if (lean_obj_tag(v_a_686_) == 0)
{
lean_del_object(v___x_688_);
goto v___jp_661_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; 
lean_dec(v_constName_655_);
v_val_690_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v_a_686_, 1);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_val_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_val_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_constName_655_);
v_a_695_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_685_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
else
{
lean_dec(v_val_673_);
goto v___jp_661_;
}
}
else
{
lean_dec(v___x_672_);
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_662_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_663_ = 0;
v___x_664_ = l_Lean_MessageData_ofConstName(v_constName_655_, v___x_663_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_662_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_667_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_710_, lean_object* v___x_711_, lean_object* v_as_x27_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
if (lean_obj_tag(v_as_x27_712_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v_b_713_);
return v___x_719_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v___x_722_; 
v_head_720_ = lean_ctor_get(v_as_x27_712_, 0);
v_tail_721_ = lean_ctor_get(v_as_x27_712_, 1);
lean_inc(v_head_720_);
v___x_722_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_720_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v_toConstantVal_724_; lean_object* v_cidx_725_; lean_object* v_numFields_726_; lean_object* v_type_727_; lean_object* v___x_728_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v_toConstantVal_724_ = lean_ctor_get(v_a_723_, 0);
lean_inc_ref(v_toConstantVal_724_);
v_cidx_725_ = lean_ctor_get(v_a_723_, 2);
lean_inc(v_cidx_725_);
v_numFields_726_ = lean_ctor_get(v_a_723_, 4);
lean_inc(v_numFields_726_);
lean_dec(v_a_723_);
v_type_727_ = lean_ctor_get(v_toConstantVal_724_, 2);
lean_inc_ref(v_type_727_);
lean_dec_ref(v_toConstantVal_724_);
v___x_728_ = l_Lean_Meta_instantiateForall(v_type_727_, v___x_711_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_746_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_746_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_746_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_746_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
uint8_t v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___f_738_; lean_object* v___x_740_; 
v___x_733_ = 0;
v___x_734_ = 1;
v___x_735_ = lean_box(v___x_733_);
v___x_736_ = lean_box(v___x_710_);
v___x_737_ = lean_box(v___x_734_);
v___f_738_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_738_, 0, v_cidx_725_);
lean_closure_set(v___f_738_, 1, v___x_735_);
lean_closure_set(v___f_738_, 2, v___x_736_);
lean_closure_set(v___f_738_, 3, v___x_737_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 1);
lean_ctor_set(v___x_731_, 0, v_numFields_726_);
v___x_740_ = v___x_731_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_numFields_726_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_729_, v___x_740_, v___f_738_, v___x_733_, v___x_733_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_Expr_app___override(v_b_713_, v_a_742_);
v_as_x27_712_ = v_tail_721_;
v_b_713_ = v___x_743_;
goto _start;
}
else
{
lean_dec_ref(v_b_713_);
return v___x_741_;
}
}
}
}
else
{
lean_dec(v_numFields_726_);
lean_dec(v_cidx_725_);
lean_dec_ref(v_b_713_);
return v___x_728_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_b_713_);
v_a_747_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_722_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_722_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v_as_x27_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_19513__boxed_764_; lean_object* v_res_765_; 
v___x_19513__boxed_764_ = lean_unbox(v___x_755_);
v_res_765_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_19513__boxed_764_, v___x_756_, v_as_x27_757_, v_b_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v_as_x27_757_);
lean_dec_ref(v___x_756_);
return v_res_765_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_box(0);
v___x_767_ = l_Lean_Level_succ___override(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_768_, uint8_t v___x_769_, uint8_t v___x_770_, uint8_t v___x_771_, lean_object* v_val_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v_ctors_778_, lean_object* v___x_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_value_787_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = l_Lean_InductiveVal_numCtors(v_val_772_);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_dec_eq(v___x_790_, v___x_791_);
lean_dec(v___x_790_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v___x_779_);
lean_inc_ref(v_x_780_);
lean_inc_ref(v___x_773_);
v___x_793_ = lean_array_push(v___x_773_, v_x_780_);
v___x_794_ = l_Lean_Meta_mkLambdaFVars(v___x_793_, v___x_774_, v___x_769_, v___x_770_, v___x_769_, v___x_770_, v___x_771_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_775_);
v___x_798_ = l_Lean_mkConst(v___x_776_, v___x_797_);
v___x_799_ = l_Lean_mkAppN(v___x_798_, v___x_777_);
v___x_800_ = l_Lean_Expr_app___override(v___x_799_, v_a_795_);
v___x_801_ = l_Lean_mkAppN(v___x_800_, v___x_773_);
lean_dec_ref(v___x_773_);
lean_inc_ref(v_x_780_);
v___x_802_ = l_Lean_Expr_app___override(v___x_801_, v_x_780_);
v___x_803_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_770_, v___x_777_, v_ctors_778_, v___x_802_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v_value_787_ = v_a_804_;
goto v___jp_786_;
}
else
{
lean_dec_ref(v_x_780_);
lean_dec_ref(v_xs_768_);
return v___x_803_;
}
}
else
{
lean_dec_ref(v_x_780_);
lean_dec(v___x_776_);
lean_dec(v___x_775_);
lean_dec_ref(v___x_773_);
lean_dec_ref(v_xs_768_);
return v___x_794_;
}
}
else
{
lean_object* v___x_805_; 
lean_dec(v___x_776_);
lean_dec(v___x_775_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
v___x_805_ = l_Lean_mkRawNatLit(v___x_779_);
v_value_787_ = v___x_805_;
goto v___jp_786_;
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_array_push(v_xs_768_, v_x_780_);
v___x_789_ = l_Lean_Meta_mkLambdaFVars(v___x_788_, v_value_787_, v___x_769_, v___x_770_, v___x_769_, v___x_770_, v___x_771_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_806_ = _args[0];
lean_object* v___x_807_ = _args[1];
lean_object* v___x_808_ = _args[2];
lean_object* v___x_809_ = _args[3];
lean_object* v_val_810_ = _args[4];
lean_object* v___x_811_ = _args[5];
lean_object* v___x_812_ = _args[6];
lean_object* v___x_813_ = _args[7];
lean_object* v___x_814_ = _args[8];
lean_object* v___x_815_ = _args[9];
lean_object* v_ctors_816_ = _args[10];
lean_object* v___x_817_ = _args[11];
lean_object* v_x_818_ = _args[12];
lean_object* v___y_819_ = _args[13];
lean_object* v___y_820_ = _args[14];
lean_object* v___y_821_ = _args[15];
lean_object* v___y_822_ = _args[16];
lean_object* v___y_823_ = _args[17];
_start:
{
uint8_t v___x_19604__boxed_824_; uint8_t v___x_19605__boxed_825_; uint8_t v___x_19606__boxed_826_; lean_object* v_res_827_; 
v___x_19604__boxed_824_ = lean_unbox(v___x_807_);
v___x_19605__boxed_825_ = lean_unbox(v___x_808_);
v___x_19606__boxed_826_ = lean_unbox(v___x_809_);
v_res_827_ = l_Lean_mkCtorIdx___lam__0(v_xs_806_, v___x_19604__boxed_824_, v___x_19605__boxed_825_, v___x_19606__boxed_826_, v_val_810_, v___x_811_, v___x_812_, v___x_813_, v___x_814_, v___x_815_, v_ctors_816_, v___x_817_, v_x_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v_ctors_816_);
lean_dec_ref(v___x_815_);
lean_dec_ref(v_val_810_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
v___x_835_ = lean_apply_6(v_k_828_, v_b_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_836_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_844_, uint8_t v_bi_845_, lean_object* v_type_846_, lean_object* v_k_847_, uint8_t v_kind_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___f_854_; lean_object* v___x_855_; 
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_854_, 0, v_k_847_);
v___x_855_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_844_, v_bi_845_, v_type_846_, v___f_854_, v_kind_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_855_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_872_, lean_object* v_bi_873_, lean_object* v_type_874_, lean_object* v_k_875_, lean_object* v_kind_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v_bi_boxed_882_; uint8_t v_kind_boxed_883_; lean_object* v_res_884_; 
v_bi_boxed_882_ = lean_unbox(v_bi_873_);
v_kind_boxed_883_ = lean_unbox(v_kind_876_);
v_res_884_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_872_, v_bi_boxed_882_, v_type_874_, v_k_875_, v_kind_boxed_883_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_885_, lean_object* v_type_886_, lean_object* v_k_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = 0;
v___x_894_ = 0;
v___x_895_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_885_, v___x_893_, v_type_886_, v_k_887_, v___x_894_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_896_, lean_object* v_type_897_, lean_object* v_k_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_896_, v_type_897_, v_k_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_xs_910_, uint8_t v___x_911_, uint8_t v___x_912_, lean_object* v_val_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v_ctors_918_, lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v_levelParams_921_, lean_object* v_indName_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
v___x_928_ = l_Lean_mkArrow(v___x_908_, v___x_909_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = 1;
v___x_931_ = l_Lean_Meta_mkForallFVars(v_xs_910_, v_a_929_, v___x_911_, v___x_912_, v___x_912_, v___x_930_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_box(v___x_911_);
v___x_934_ = lean_box(v___x_912_);
v___x_935_ = lean_box(v___x_930_);
lean_inc_ref(v_val_913_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_936_, 0, v_xs_910_);
lean_closure_set(v___f_936_, 1, v___x_933_);
lean_closure_set(v___f_936_, 2, v___x_934_);
lean_closure_set(v___f_936_, 3, v___x_935_);
lean_closure_set(v___f_936_, 4, v_val_913_);
lean_closure_set(v___f_936_, 5, v___x_914_);
lean_closure_set(v___f_936_, 6, v___x_909_);
lean_closure_set(v___f_936_, 7, v___x_915_);
lean_closure_set(v___f_936_, 8, v___x_916_);
lean_closure_set(v___f_936_, 9, v___x_917_);
lean_closure_set(v___f_936_, 10, v_ctors_918_);
lean_closure_set(v___f_936_, 11, v___x_919_);
v___x_937_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_938_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_937_, v___x_908_, v___f_936_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v_env_941_; uint32_t v___x_942_; uint32_t v___x_943_; uint32_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1075_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc_n(v_a_939_, 2);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = lean_st_ref_get(v___y_926_);
v_env_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_ref(v_env_941_);
lean_dec(v___x_940_);
v___x_942_ = l_Lean_getMaxHeight(v_env_941_, v_a_939_);
v___x_943_ = 1;
v___x_944_ = lean_uint32_add(v___x_942_, v___x_943_);
v___x_945_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_945_, 0, v___x_944_);
lean_inc(v___x_920_);
v___x_946_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_920_, v_levelParams_921_, v_a_932_, v_a_939_, v___x_945_, v___y_926_);
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_1075_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1075_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 1);
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_1074_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___x_1000_; 
lean_inc_ref(v___x_952_);
v___x_1000_ = l_Lean_addDecl(v___x_952_, v___x_911_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; lean_object* v_env_1002_; lean_object* v_nextMacroScope_1003_; lean_object* v_ngen_1004_; lean_object* v_auxDeclNGen_1005_; lean_object* v_traceState_1006_; lean_object* v_messages_1007_; lean_object* v_infoState_1008_; lean_object* v_snapshotTasks_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref_known(v___x_1000_, 1);
v___x_1001_ = lean_st_ref_take(v___y_926_);
v_env_1002_ = lean_ctor_get(v___x_1001_, 0);
v_nextMacroScope_1003_ = lean_ctor_get(v___x_1001_, 1);
v_ngen_1004_ = lean_ctor_get(v___x_1001_, 2);
v_auxDeclNGen_1005_ = lean_ctor_get(v___x_1001_, 3);
v_traceState_1006_ = lean_ctor_get(v___x_1001_, 4);
v_messages_1007_ = lean_ctor_get(v___x_1001_, 6);
v_infoState_1008_ = lean_ctor_get(v___x_1001_, 7);
v_snapshotTasks_1009_ = lean_ctor_get(v___x_1001_, 8);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1001_, 5);
lean_dec(v_unused_1073_);
v___x_1011_ = v___x_1001_;
v_isShared_1012_ = v_isSharedCheck_1072_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snapshotTasks_1009_);
lean_inc(v_infoState_1008_);
lean_inc(v_messages_1007_);
lean_inc(v_traceState_1006_);
lean_inc(v_auxDeclNGen_1005_);
lean_inc(v_ngen_1004_);
lean_inc(v_nextMacroScope_1003_);
lean_inc(v_env_1002_);
lean_dec(v___x_1001_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1072_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc(v___x_920_);
v___x_1013_ = l_Lean_Meta_addToCompletionBlackList(v_env_1002_, v___x_920_);
v___x_1014_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 5, v___x_1014_);
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_nextMacroScope_1003_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_ngen_1004_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_auxDeclNGen_1005_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_traceState_1006_);
lean_ctor_set(v_reuseFailAlloc_1071_, 5, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1071_, 6, v_messages_1007_);
lean_ctor_set(v_reuseFailAlloc_1071_, 7, v_infoState_1008_);
lean_ctor_set(v_reuseFailAlloc_1071_, 8, v_snapshotTasks_1009_);
v___x_1016_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_mctx_1019_; lean_object* v_zetaDeltaFVarIds_1020_; lean_object* v_postponed_1021_; lean_object* v_diag_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1069_; 
v___x_1017_ = lean_st_ref_put(v___y_926_, v___x_1016_);
v___x_1018_ = lean_st_ref_take(v___y_924_);
v_mctx_1019_ = lean_ctor_get(v___x_1018_, 0);
v_zetaDeltaFVarIds_1020_ = lean_ctor_get(v___x_1018_, 2);
v_postponed_1021_ = lean_ctor_get(v___x_1018_, 3);
v_diag_1022_ = lean_ctor_get(v___x_1018_, 4);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v___x_1018_, 1);
lean_dec(v_unused_1070_);
v___x_1024_ = v___x_1018_;
v_isShared_1025_ = v_isSharedCheck_1069_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_diag_1022_);
lean_inc(v_postponed_1021_);
lean_inc(v_zetaDeltaFVarIds_1020_);
lean_inc(v_mctx_1019_);
lean_dec(v___x_1018_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1069_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_mctx_1019_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_zetaDeltaFVarIds_1020_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_postponed_1021_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_diag_1022_);
v___x_1028_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_env_1031_; lean_object* v_nextMacroScope_1032_; lean_object* v_ngen_1033_; lean_object* v_auxDeclNGen_1034_; lean_object* v_traceState_1035_; lean_object* v_messages_1036_; lean_object* v_infoState_1037_; lean_object* v_snapshotTasks_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1066_; 
v___x_1029_ = lean_st_ref_put(v___y_924_, v___x_1028_);
v___x_1030_ = lean_st_ref_take(v___y_926_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
v_nextMacroScope_1032_ = lean_ctor_get(v___x_1030_, 1);
v_ngen_1033_ = lean_ctor_get(v___x_1030_, 2);
v_auxDeclNGen_1034_ = lean_ctor_get(v___x_1030_, 3);
v_traceState_1035_ = lean_ctor_get(v___x_1030_, 4);
v_messages_1036_ = lean_ctor_get(v___x_1030_, 6);
v_infoState_1037_ = lean_ctor_get(v___x_1030_, 7);
v_snapshotTasks_1038_ = lean_ctor_get(v___x_1030_, 8);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1030_, 5);
lean_dec(v_unused_1067_);
v___x_1040_ = v___x_1030_;
v_isShared_1041_ = v_isSharedCheck_1066_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snapshotTasks_1038_);
lean_inc(v_infoState_1037_);
lean_inc(v_messages_1036_);
lean_inc(v_traceState_1035_);
lean_inc(v_auxDeclNGen_1034_);
lean_inc(v_ngen_1033_);
lean_inc(v_nextMacroScope_1032_);
lean_inc(v_env_1031_);
lean_dec(v___x_1030_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1066_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_inc(v___x_920_);
v___x_1042_ = l_Lean_addProtected(v_env_1031_, v___x_920_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 5, v___x_1014_);
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_nextMacroScope_1032_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_ngen_1033_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_auxDeclNGen_1034_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_traceState_1035_);
lean_ctor_set(v_reuseFailAlloc_1065_, 5, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1065_, 6, v_messages_1036_);
lean_ctor_set(v_reuseFailAlloc_1065_, 7, v_infoState_1037_);
lean_ctor_set(v_reuseFailAlloc_1065_, 8, v_snapshotTasks_1038_);
v___x_1044_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_mctx_1047_; lean_object* v_zetaDeltaFVarIds_1048_; lean_object* v_postponed_1049_; lean_object* v_diag_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1063_; 
v___x_1045_ = lean_st_ref_put(v___y_926_, v___x_1044_);
v___x_1046_ = lean_st_ref_take(v___y_924_);
v_mctx_1047_ = lean_ctor_get(v___x_1046_, 0);
v_zetaDeltaFVarIds_1048_ = lean_ctor_get(v___x_1046_, 2);
v_postponed_1049_ = lean_ctor_get(v___x_1046_, 3);
v_diag_1050_ = lean_ctor_get(v___x_1046_, 4);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1046_, 1);
lean_dec(v_unused_1064_);
v___x_1052_ = v___x_1046_;
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_diag_1050_);
lean_inc(v_postponed_1049_);
lean_inc(v_zetaDeltaFVarIds_1048_);
lean_inc(v_mctx_1047_);
lean_dec(v___x_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___x_1026_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_mctx_1047_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_zetaDeltaFVarIds_1048_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_postponed_1049_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_diag_1050_);
v___x_1055_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = lean_st_ref_put(v___y_924_, v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = l_Lean_InductiveVal_numCtors(v_val_913_);
lean_dec_ref(v_val_913_);
v___x_1059_ = lean_nat_dec_eq(v___x_1058_, v___x_1057_);
lean_dec(v___x_1058_);
if (v___x_1059_ == 0)
{
v___y_959_ = v___y_924_;
v___y_960_ = v___y_925_;
v___y_961_ = v___y_926_;
goto v___jp_958_;
}
else
{
uint8_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = 2;
lean_inc(v___x_920_);
v___x_1061_ = l_Lean_Meta_setInlineAttribute(v___x_920_, v___x_1060_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_dec_ref_known(v___x_1061_, 1);
v___y_959_ = v___y_924_;
v___y_960_ = v___y_925_;
v___y_961_ = v___y_926_;
goto v___jp_958_;
}
else
{
lean_dec_ref(v___x_952_);
lean_dec(v_indName_922_);
lean_dec(v___x_920_);
return v___x_1061_;
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
else
{
lean_dec_ref(v___x_952_);
lean_dec(v_indName_922_);
lean_dec(v___x_920_);
lean_dec_ref(v_val_913_);
return v___x_1000_;
}
v___jp_953_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_compileDecl(v___x_952_, v___x_912_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; 
lean_dec_ref_known(v___x_956_, 1);
v___x_957_ = l_Lean_enableRealizationsForConst(v___x_920_, v___y_954_, v___y_955_);
return v___x_957_;
}
else
{
lean_dec(v___x_920_);
return v___x_956_;
}
}
v___jp_958_:
{
lean_object* v___x_962_; lean_object* v_env_963_; uint8_t v___x_964_; 
v___x_962_ = lean_st_ref_get(v___y_961_);
v_env_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_env_963_);
lean_dec(v___x_962_);
v___x_964_ = l_Lean_isMarkedMeta(v_env_963_, v_indName_922_);
if (v___x_964_ == 0)
{
v___y_954_ = v___y_960_;
v___y_955_ = v___y_961_;
goto v___jp_953_;
}
else
{
lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v_nextMacroScope_967_; lean_object* v_ngen_968_; lean_object* v_auxDeclNGen_969_; lean_object* v_traceState_970_; lean_object* v_messages_971_; lean_object* v_infoState_972_; lean_object* v_snapshotTasks_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_998_; 
v___x_965_ = lean_st_ref_take(v___y_961_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
v_nextMacroScope_967_ = lean_ctor_get(v___x_965_, 1);
v_ngen_968_ = lean_ctor_get(v___x_965_, 2);
v_auxDeclNGen_969_ = lean_ctor_get(v___x_965_, 3);
v_traceState_970_ = lean_ctor_get(v___x_965_, 4);
v_messages_971_ = lean_ctor_get(v___x_965_, 6);
v_infoState_972_ = lean_ctor_get(v___x_965_, 7);
v_snapshotTasks_973_ = lean_ctor_get(v___x_965_, 8);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_965_, 5);
lean_dec(v_unused_999_);
v___x_975_ = v___x_965_;
v_isShared_976_ = v_isSharedCheck_998_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snapshotTasks_973_);
lean_inc(v_infoState_972_);
lean_inc(v_messages_971_);
lean_inc(v_traceState_970_);
lean_inc(v_auxDeclNGen_969_);
lean_inc(v_ngen_968_);
lean_inc(v_nextMacroScope_967_);
lean_inc(v_env_966_);
lean_dec(v___x_965_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_998_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
lean_inc(v___x_920_);
v___x_977_ = l_Lean_markMeta(v_env_966_, v___x_920_);
v___x_978_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__2);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 5, v___x_978_);
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_967_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_968_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_969_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_traceState_970_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_messages_971_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_infoState_972_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_snapshotTasks_973_);
v___x_980_ = v_reuseFailAlloc_997_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_mctx_983_; lean_object* v_zetaDeltaFVarIds_984_; lean_object* v_postponed_985_; lean_object* v_diag_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_995_; 
v___x_981_ = lean_st_ref_put(v___y_961_, v___x_980_);
v___x_982_ = lean_st_ref_take(v___y_959_);
v_mctx_983_ = lean_ctor_get(v___x_982_, 0);
v_zetaDeltaFVarIds_984_ = lean_ctor_get(v___x_982_, 2);
v_postponed_985_ = lean_ctor_get(v___x_982_, 3);
v_diag_986_ = lean_ctor_get(v___x_982_, 4);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_982_, 1);
lean_dec(v_unused_996_);
v___x_988_ = v___x_982_;
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_diag_986_);
lean_inc(v_postponed_985_);
lean_inc(v_zetaDeltaFVarIds_984_);
lean_inc(v_mctx_983_);
lean_dec(v___x_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg___closed__3);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_mctx_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_zetaDeltaFVarIds_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_postponed_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_diag_986_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_st_ref_put(v___y_959_, v___x_992_);
v___y_954_ = v___y_960_;
v___y_955_ = v___y_961_;
goto v___jp_953_;
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
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_932_);
lean_dec(v_indName_922_);
lean_dec(v_levelParams_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_val_913_);
v_a_1076_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_938_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_938_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_indName_922_);
lean_dec(v_levelParams_921_);
lean_dec(v___x_920_);
lean_dec(v___x_919_);
lean_dec(v_ctors_918_);
lean_dec_ref(v___x_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_val_913_);
lean_dec_ref(v_xs_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
v_a_1084_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_931_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_931_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_indName_922_);
lean_dec(v_levelParams_921_);
lean_dec(v___x_920_);
lean_dec(v___x_919_);
lean_dec(v_ctors_918_);
lean_dec_ref(v___x_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_val_913_);
lean_dec_ref(v_xs_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
v_a_1092_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_928_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_928_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1100_ = _args[0];
lean_object* v___x_1101_ = _args[1];
lean_object* v_xs_1102_ = _args[2];
lean_object* v___x_1103_ = _args[3];
lean_object* v___x_1104_ = _args[4];
lean_object* v_val_1105_ = _args[5];
lean_object* v___x_1106_ = _args[6];
lean_object* v___x_1107_ = _args[7];
lean_object* v___x_1108_ = _args[8];
lean_object* v___x_1109_ = _args[9];
lean_object* v_ctors_1110_ = _args[10];
lean_object* v___x_1111_ = _args[11];
lean_object* v___x_1112_ = _args[12];
lean_object* v_levelParams_1113_ = _args[13];
lean_object* v_indName_1114_ = _args[14];
lean_object* v___y_1115_ = _args[15];
lean_object* v___y_1116_ = _args[16];
lean_object* v___y_1117_ = _args[17];
lean_object* v___y_1118_ = _args[18];
lean_object* v___y_1119_ = _args[19];
_start:
{
uint8_t v___x_19814__boxed_1120_; uint8_t v___x_19815__boxed_1121_; lean_object* v_res_1122_; 
v___x_19814__boxed_1120_ = lean_unbox(v___x_1103_);
v___x_19815__boxed_1121_ = lean_unbox(v___x_1104_);
v_res_1122_ = l_Lean_mkCtorIdx___lam__1(v___x_1100_, v___x_1101_, v_xs_1102_, v___x_19814__boxed_1120_, v___x_19815__boxed_1121_, v_val_1105_, v___x_1106_, v___x_1107_, v___x_1108_, v___x_1109_, v_ctors_1110_, v___x_1111_, v___x_1112_, v_levelParams_1113_, v_indName_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13(size_t v_sz_1123_, size_t v_i_1124_, lean_object* v_bs_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_lt(v_i_1124_, v_sz_1123_);
if (v___x_1126_ == 0)
{
return v_bs_1125_;
}
else
{
lean_object* v_v_1127_; lean_object* v___x_1128_; lean_object* v_bs_x27_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v_v_1127_ = lean_array_uget(v_bs_1125_, v_i_1124_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v_bs_x27_1129_ = lean_array_uset(v_bs_1125_, v_i_1124_, v___x_1128_);
v___x_1130_ = l_Lean_Expr_fvarId_x21(v_v_1127_);
lean_dec(v_v_1127_);
v___x_1131_ = 1;
v___x_1132_ = lean_box(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1130_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1124_, v___x_1134_);
v___x_1136_ = lean_array_uset(v_bs_x27_1129_, v_i_1124_, v___x_1133_);
v_i_1124_ = v___x_1135_;
v_bs_1125_ = v___x_1136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_bs_1140_){
_start:
{
size_t v_sz_boxed_1141_; size_t v_i_boxed_1142_; lean_object* v_res_1143_; 
v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1142_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13(v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg(lean_object* v_bs_1144_, lean_object* v_k_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1144_, v_k_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1151_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1151_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg___boxed(lean_object* v_bs_1168_, lean_object* v_k_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg(v_bs_1168_, v_k_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_bs_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg(lean_object* v_bs_1176_, lean_object* v_k_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
size_t v_sz_1183_; size_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_sz_1183_ = lean_array_size(v_bs_1176_);
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__13(v_sz_1183_, v___x_1184_, v_bs_1176_);
v___x_1186_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg(v___x_1185_, v_k_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec_ref(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg___boxed(lean_object* v_bs_1187_, lean_object* v_k_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg(v_bs_1187_, v_k_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1198_, lean_object* v_indName_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, uint8_t v___x_1202_, uint8_t v___x_1203_, lean_object* v_val_1204_, lean_object* v___x_1205_, lean_object* v_ctors_1206_, lean_object* v___x_1207_, lean_object* v_levelParams_1208_, lean_object* v_xs_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1198_);
lean_inc_ref_n(v_xs_1209_, 3);
v___x_1217_ = l_Array_toSubarray___redArg(v_xs_1209_, v___x_1216_, v_numParams_1198_);
v___x_1218_ = l_Subarray_copy___redArg(v___x_1217_);
v___x_1219_ = lean_array_get_size(v_xs_1209_);
v___x_1220_ = l_Array_toSubarray___redArg(v_xs_1209_, v_numParams_1198_, v___x_1219_);
v___x_1221_ = l_Subarray_copy___redArg(v___x_1220_);
lean_inc(v___x_1200_);
lean_inc(v_indName_1199_);
v___x_1222_ = l_Lean_mkConst(v_indName_1199_, v___x_1200_);
v___x_1223_ = l_Lean_mkAppN(v___x_1222_, v_xs_1209_);
v___x_1224_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1225_ = l_Lean_mkConst(v___x_1224_, v___x_1201_);
v___x_1226_ = lean_box(v___x_1202_);
v___x_1227_ = lean_box(v___x_1203_);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1228_, 0, v___x_1223_);
lean_closure_set(v___f_1228_, 1, v___x_1225_);
lean_closure_set(v___f_1228_, 2, v_xs_1209_);
lean_closure_set(v___f_1228_, 3, v___x_1226_);
lean_closure_set(v___f_1228_, 4, v___x_1227_);
lean_closure_set(v___f_1228_, 5, v_val_1204_);
lean_closure_set(v___f_1228_, 6, v___x_1221_);
lean_closure_set(v___f_1228_, 7, v___x_1200_);
lean_closure_set(v___f_1228_, 8, v___x_1205_);
lean_closure_set(v___f_1228_, 9, v___x_1218_);
lean_closure_set(v___f_1228_, 10, v_ctors_1206_);
lean_closure_set(v___f_1228_, 11, v___x_1216_);
lean_closure_set(v___f_1228_, 12, v___x_1207_);
lean_closure_set(v___f_1228_, 13, v_levelParams_1208_);
lean_closure_set(v___f_1228_, 14, v_indName_1199_);
v___x_1229_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg(v_xs_1209_, v___f_1228_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1230_ = _args[0];
lean_object* v_indName_1231_ = _args[1];
lean_object* v___x_1232_ = _args[2];
lean_object* v___x_1233_ = _args[3];
lean_object* v___x_1234_ = _args[4];
lean_object* v___x_1235_ = _args[5];
lean_object* v_val_1236_ = _args[6];
lean_object* v___x_1237_ = _args[7];
lean_object* v_ctors_1238_ = _args[8];
lean_object* v___x_1239_ = _args[9];
lean_object* v_levelParams_1240_ = _args[10];
lean_object* v_xs_1241_ = _args[11];
lean_object* v_x_1242_ = _args[12];
lean_object* v___y_1243_ = _args[13];
lean_object* v___y_1244_ = _args[14];
lean_object* v___y_1245_ = _args[15];
lean_object* v___y_1246_ = _args[16];
lean_object* v___y_1247_ = _args[17];
_start:
{
uint8_t v___x_20236__boxed_1248_; uint8_t v___x_20237__boxed_1249_; lean_object* v_res_1250_; 
v___x_20236__boxed_1248_ = lean_unbox(v___x_1234_);
v___x_20237__boxed_1249_ = lean_unbox(v___x_1235_);
v_res_1250_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1230_, v_indName_1231_, v___x_1232_, v___x_1233_, v___x_20236__boxed_1248_, v___x_20237__boxed_1249_, v_val_1236_, v___x_1237_, v_ctors_1238_, v___x_1239_, v_levelParams_1240_, v_xs_1241_, v_x_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_x_1242_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
if (lean_obj_tag(v_a_1251_) == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = l_List_reverse___redArg(v_a_1252_);
return v___x_1253_;
}
else
{
lean_object* v_head_1254_; lean_object* v_tail_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_head_1254_ = lean_ctor_get(v_a_1251_, 0);
v_tail_1255_ = lean_ctor_get(v_a_1251_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1251_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v_a_1251_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_tail_1255_);
lean_inc(v_head_1254_);
lean_dec(v_a_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_mkLevelParam(v_head_1254_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_a_1252_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1252_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v_a_1251_ = v_tail_1255_;
v_a_1252_ = v___x_1261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg(lean_object* v_ref_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_toCold_1272_; lean_object* v_options_1273_; lean_object* v_currRecDepth_1274_; lean_object* v_maxRecDepth_1275_; lean_object* v_ref_1276_; lean_object* v_currNamespace_1277_; lean_object* v_openDecls_1278_; lean_object* v_initHeartbeats_1279_; lean_object* v_maxHeartbeats_1280_; lean_object* v_currMacroScope_1281_; uint8_t v_diag_1282_; uint8_t v_suppressElabErrors_1283_; lean_object* v_ref_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_toCold_1272_ = lean_ctor_get(v___y_1269_, 0);
v_options_1273_ = lean_ctor_get(v___y_1269_, 1);
v_currRecDepth_1274_ = lean_ctor_get(v___y_1269_, 2);
v_maxRecDepth_1275_ = lean_ctor_get(v___y_1269_, 3);
v_ref_1276_ = lean_ctor_get(v___y_1269_, 4);
v_currNamespace_1277_ = lean_ctor_get(v___y_1269_, 5);
v_openDecls_1278_ = lean_ctor_get(v___y_1269_, 6);
v_initHeartbeats_1279_ = lean_ctor_get(v___y_1269_, 7);
v_maxHeartbeats_1280_ = lean_ctor_get(v___y_1269_, 8);
v_currMacroScope_1281_ = lean_ctor_get(v___y_1269_, 9);
v_diag_1282_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*10);
v_suppressElabErrors_1283_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*10 + 1);
v_ref_1284_ = l_Lean_replaceRef(v_ref_1265_, v_ref_1276_);
lean_inc(v_currMacroScope_1281_);
lean_inc(v_maxHeartbeats_1280_);
lean_inc(v_initHeartbeats_1279_);
lean_inc(v_openDecls_1278_);
lean_inc(v_currNamespace_1277_);
lean_inc(v_maxRecDepth_1275_);
lean_inc(v_currRecDepth_1274_);
lean_inc_ref(v_options_1273_);
lean_inc_ref(v_toCold_1272_);
v___x_1285_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1285_, 0, v_toCold_1272_);
lean_ctor_set(v___x_1285_, 1, v_options_1273_);
lean_ctor_set(v___x_1285_, 2, v_currRecDepth_1274_);
lean_ctor_set(v___x_1285_, 3, v_maxRecDepth_1275_);
lean_ctor_set(v___x_1285_, 4, v_ref_1284_);
lean_ctor_set(v___x_1285_, 5, v_currNamespace_1277_);
lean_ctor_set(v___x_1285_, 6, v_openDecls_1278_);
lean_ctor_set(v___x_1285_, 7, v_initHeartbeats_1279_);
lean_ctor_set(v___x_1285_, 8, v_maxHeartbeats_1280_);
lean_ctor_set(v___x_1285_, 9, v_currMacroScope_1281_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*10, v_diag_1282_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*10 + 1, v_suppressElabErrors_1283_);
v___x_1286_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___x_1285_, v___y_1270_);
lean_dec_ref_known(v___x_1285_, 10);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg___boxed(lean_object* v_ref_1287_, lean_object* v_msg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg(v_ref_1287_, v_msg_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v_ref_1287_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0(void){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__0);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
lean_ctor_set(v___x_1300_, 4, v___x_1298_);
lean_ctor_set(v___x_1300_, 5, v___x_1298_);
lean_ctor_set(v___x_1300_, 6, v___x_1298_);
lean_ctor_set(v___x_1300_, 7, v___x_1298_);
lean_ctor_set(v___x_1300_, 8, v___x_1298_);
lean_ctor_set(v___x_1300_, 9, v___x_1298_);
lean_ctor_set(v___x_1300_, 10, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(32u);
v___x_1302_ = lean_mk_empty_array_with_capacity(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4(void){
_start:
{
size_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((size_t)5ULL);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_unsigned_to_nat(32u);
v___x_1307_ = lean_mk_empty_array_with_capacity(v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__3);
v___x_1309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
lean_ctor_set(v___x_1309_, 2, v___x_1305_);
lean_ctor_set(v___x_1309_, 3, v___x_1305_);
lean_ctor_set_usize(v___x_1309_, 4, v___x_1304_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_box(1);
v___x_1311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__4);
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__1);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v___x_1310_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__6));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__8));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__10));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__12));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__14));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__16));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__18));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg(lean_object* v_msg_1335_, lean_object* v_declHint_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; lean_object* v_env_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_st_ref_get(v___y_1337_);
v_env_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_env_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = l_Lean_Name_isAnonymous(v_declHint_1336_);
if (v___x_1341_ == 0)
{
uint8_t v_isExporting_1342_; 
v_isExporting_1342_ = lean_ctor_get_uint8(v_env_1340_, sizeof(void*)*8);
if (v_isExporting_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref(v_env_1340_);
lean_dec(v_declHint_1336_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_msg_1335_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_inc_ref(v_env_1340_);
v___x_1344_ = l_Lean_Environment_setExporting(v_env_1340_, v___x_1341_);
lean_inc(v_declHint_1336_);
lean_inc_ref(v___x_1344_);
v___x_1345_ = l_Lean_Environment_contains(v___x_1344_, v_declHint_1336_, v_isExporting_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v___x_1344_);
lean_dec_ref(v_env_1340_);
lean_dec(v_declHint_1336_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_msg_1335_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_c_1352_; lean_object* v___x_1353_; 
v___x_1347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__2);
v___x_1348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__5);
v___x_1349_ = l_Lean_Options_empty;
v___x_1350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1344_);
lean_ctor_set(v___x_1350_, 1, v___x_1347_);
lean_ctor_set(v___x_1350_, 2, v___x_1348_);
lean_ctor_set(v___x_1350_, 3, v___x_1349_);
lean_inc(v_declHint_1336_);
v___x_1351_ = l_Lean_MessageData_ofConstName(v_declHint_1336_, v___x_1341_);
v_c_1352_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1352_, 0, v___x_1350_);
lean_ctor_set(v_c_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1340_, v_declHint_1336_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_env_1340_);
lean_dec(v_declHint_1336_);
v___x_1354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_c_1352_);
v___x_1356_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__9);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_MessageData_note(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_msg_1335_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1396_; 
v_val_1361_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1363_ = v___x_1353_;
v_isShared_1364_ = v_isSharedCheck_1396_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v___x_1353_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1396_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_mod_1368_; uint8_t v___x_1369_; 
v___x_1365_ = lean_box(0);
v___x_1366_ = l_Lean_Environment_header(v_env_1340_);
lean_dec_ref(v_env_1340_);
v___x_1367_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1366_);
v_mod_1368_ = lean_array_get(v___x_1365_, v___x_1367_, v_val_1361_);
lean_dec(v_val_1361_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = l_Lean_isPrivateName(v_declHint_1336_);
lean_dec(v_declHint_1336_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__11);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_c_1352_);
v___x_1372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__13);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_MessageData_ofName(v_mod_1368_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__15);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_MessageData_note(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_msg_1335_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1379_);
v___x_1381_ = v___x_1363_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__7);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v_c_1352_);
v___x_1385_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__17);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_MessageData_ofName(v_mod_1368_);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___closed__19);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = l_Lean_MessageData_note(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_msg_1335_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1392_);
v___x_1394_ = v___x_1363_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1397_; 
lean_dec_ref(v_env_1340_);
lean_dec(v_declHint_1336_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_msg_1335_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg___boxed(lean_object* v_msg_1398_, lean_object* v_declHint_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg(v_msg_1398_, v_declHint_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20(lean_object* v_msg_1403_, lean_object* v_declHint_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v___x_1410_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg(v_msg_1403_, v_declHint_1404_, v___y_1408_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = l_Lean_unknownIdentifierMessageTag;
v___x_1416_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_a_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20___boxed(lean_object* v_msg_1421_, lean_object* v_declHint_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20(v_msg_1421_, v_declHint_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg(lean_object* v_ref_1429_, lean_object* v_msg_1430_, lean_object* v_declHint_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20(v_msg_1430_, v_declHint_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg(v_ref_1429_, v_a_1438_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v_declHint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg(v_ref_1440_, v_msg_1441_, v_declHint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v_ref_1440_);
return v_res_1448_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1452_, lean_object* v_constName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1459_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1460_ = 0;
lean_inc(v_constName_1453_);
v___x_1461_ = l_Lean_MessageData_ofConstName(v_constName_1453_, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1459_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg(v_ref_1452_, v___x_1464_, v_constName_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1466_, lean_object* v_constName_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1466_, v_constName_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_ref_1466_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_ref_1480_; lean_object* v___x_1481_; 
v_ref_1480_ = lean_ctor_get(v___y_1477_, 4);
v___x_1481_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1480_, v_constName_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_env_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_st_ref_get(v___y_1493_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_env_1496_);
lean_dec(v___x_1495_);
v___x_1497_ = 0;
lean_inc(v_constName_1489_);
v___x_1498_ = l_Lean_Environment_find_x3f(v_env_1496_, v_constName_1489_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_constName_1489_);
v_val_1500_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 0);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1500_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1517_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1518_ = lean_unsigned_to_nat(62u);
v___x_1519_ = lean_unsigned_to_nat(47u);
v___x_1520_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1521_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1522_ = l_mkPanicMessageWithDecl(v___x_1521_, v___x_1520_, v___x_1519_, v___x_1518_, v___x_1517_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1523_, uint8_t v___x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_options_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_options_1530_ = lean_ctor_get(v___y_1527_, 1);
v___x_1531_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1532_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_options_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_indName_1523_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1621_; 
lean_inc(v_indName_1523_);
v___x_1535_ = l_Lean_mkCtorIdxName(v_indName_1523_);
lean_inc(v___x_1535_);
v___x_1536_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1535_, v___x_1532_, v___y_1528_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1621_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1621_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_unbox(v_a_1537_);
lean_dec(v_a_1537_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_del_object(v___x_1539_);
lean_inc(v_indName_1523_);
v___x_1542_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1523_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
if (lean_obj_tag(v_a_1543_) == 5)
{
lean_object* v_val_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1606_; 
v_val_1544_ = lean_ctor_get(v_a_1543_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1546_ = v_a_1543_;
v_isShared_1547_ = v_isSharedCheck_1606_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_val_1544_);
lean_dec(v_a_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1606_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_toConstantVal_1548_; lean_object* v_numParams_1549_; lean_object* v_numIndices_1550_; lean_object* v_ctors_1551_; lean_object* v_levelParams_1552_; lean_object* v_type_1553_; lean_object* v___x_1554_; 
v_toConstantVal_1548_ = lean_ctor_get(v_val_1544_, 0);
v_numParams_1549_ = lean_ctor_get(v_val_1544_, 1);
lean_inc(v_numParams_1549_);
v_numIndices_1550_ = lean_ctor_get(v_val_1544_, 2);
lean_inc(v_numIndices_1550_);
v_ctors_1551_ = lean_ctor_get(v_val_1544_, 4);
lean_inc(v_ctors_1551_);
v_levelParams_1552_ = lean_ctor_get(v_toConstantVal_1548_, 1);
lean_inc(v_levelParams_1552_);
v_type_1553_ = lean_ctor_get(v_toConstantVal_1548_, 2);
lean_inc_ref_n(v_type_1553_, 2);
v___x_1554_ = l_Lean_Meta_isPropFormerType(v_type_1553_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1597_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1597_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1597_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_unbox(v_a_1555_);
lean_dec(v_a_1555_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_del_object(v___x_1557_);
lean_inc(v_indName_1523_);
v___x_1560_ = l_Lean_mkCasesOnName(v_indName_1523_);
lean_inc(v___x_1560_);
v___x_1561_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_1560_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1584_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1584_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1584_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1566_ = l_List_lengthTR___redArg(v_levelParams_1552_);
v___x_1567_ = l_Lean_ConstantInfo_levelParams(v_a_1562_);
lean_dec(v_a_1562_);
v___x_1568_ = l_List_lengthTR___redArg(v___x_1567_);
lean_dec(v___x_1567_);
v___x_1569_ = lean_nat_dec_lt(v___x_1566_, v___x_1568_);
lean_dec(v___x_1568_);
lean_dec(v___x_1566_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_dec(v___x_1560_);
lean_dec_ref(v_type_1553_);
lean_dec(v_levelParams_1552_);
lean_dec(v_ctors_1551_);
lean_dec(v_numIndices_1550_);
lean_dec(v_numParams_1549_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_val_1544_);
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v___x_1570_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1570_);
v___x_1572_ = v___x_1564_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_del_object(v___x_1564_);
v___x_1574_ = lean_box(0);
lean_inc(v_levelParams_1552_);
v___x_1575_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1552_, v___x_1574_);
v___x_1576_ = lean_box(v___x_1524_);
v___x_1577_ = lean_box(v___x_1532_);
lean_inc(v_numParams_1549_);
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1578_, 0, v_numParams_1549_);
lean_closure_set(v___f_1578_, 1, v_indName_1523_);
lean_closure_set(v___f_1578_, 2, v___x_1575_);
lean_closure_set(v___f_1578_, 3, v___x_1574_);
lean_closure_set(v___f_1578_, 4, v___x_1576_);
lean_closure_set(v___f_1578_, 5, v___x_1577_);
lean_closure_set(v___f_1578_, 6, v_val_1544_);
lean_closure_set(v___f_1578_, 7, v___x_1560_);
lean_closure_set(v___f_1578_, 8, v_ctors_1551_);
lean_closure_set(v___f_1578_, 9, v___x_1535_);
lean_closure_set(v___f_1578_, 10, v_levelParams_1552_);
v___x_1579_ = lean_nat_add(v_numParams_1549_, v_numIndices_1550_);
lean_dec(v_numIndices_1550_);
lean_dec(v_numParams_1549_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1579_);
v___x_1581_ = v___x_1546_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1553_, v___x_1581_, v___f_1578_, v___x_1524_, v___x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v___x_1560_);
lean_dec_ref(v_type_1553_);
lean_dec(v_levelParams_1552_);
lean_dec(v_ctors_1551_);
lean_dec(v_numIndices_1550_);
lean_dec(v_numParams_1549_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_val_1544_);
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v_a_1585_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1561_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1561_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec_ref(v_type_1553_);
lean_dec(v_levelParams_1552_);
lean_dec(v_ctors_1551_);
lean_dec(v_numIndices_1550_);
lean_dec(v_numParams_1549_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_val_1544_);
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v___x_1593_ = lean_box(0);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1593_);
v___x_1595_ = v___x_1557_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v_type_1553_);
lean_dec(v_levelParams_1552_);
lean_dec(v_ctors_1551_);
lean_dec(v_numIndices_1550_);
lean_dec(v_numParams_1549_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_val_1544_);
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v_a_1598_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1554_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1554_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_a_1543_);
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v___x_1607_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_1608_ = l_panic___at___00Lean_mkCtorIdx_spec__10(v___x_1607_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1608_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v_a_1609_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1542_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1542_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v___x_1535_);
lean_dec(v_indName_1523_);
v___x_1617_ = lean_box(0);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1617_);
v___x_1619_ = v___x_1539_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_1622_, lean_object* v___x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v___x_20784__boxed_1629_; lean_object* v_res_1630_; 
v___x_20784__boxed_1629_ = lean_unbox(v___x_1623_);
v_res_1630_ = l_Lean_mkCtorIdx___lam__3(v_indName_1622_, v___x_20784__boxed_1629_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_1631_, lean_object* v_e_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Lean_indentD(v_e_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_1635_, lean_object* v___f_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1635_, v___f_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1642_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_1659_, lean_object* v___f_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_mkCtorIdx___lam__5(v___f_1659_, v___f_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1666_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_1672_ = l_Lean_stringToMessageData(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; uint8_t v___x_1689_; 
v___x_1679_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_1680_ = 0;
v___x_1681_ = lean_box(v___x_1680_);
lean_inc_n(v_indName_1673_, 2);
v___f_1682_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1682_, 0, v_indName_1673_);
lean_closure_set(v___f_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_MessageData_ofConstName(v_indName_1673_, v___x_1680_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1679_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_1687_, 0, v___x_1686_);
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1688_, 0, v___f_1682_);
lean_closure_set(v___f_1688_, 1, v___f_1687_);
v___x_1689_ = l_Lean_isPrivateName(v_indName_1673_);
lean_dec(v_indName_1673_);
if (v___x_1689_ == 0)
{
uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = 1;
v___x_1691_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(v___f_1688_, v___x_1690_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__11___redArg(v___f_1688_, v___x_1680_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_mkCtorIdx(v_indName_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_1700_, lean_object* v___x_1701_, lean_object* v_as_1702_, lean_object* v_as_x27_1703_, lean_object* v_b_1704_, lean_object* v_a_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1700_, v___x_1701_, v_as_x27_1703_, v_b_1704_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_1712_, lean_object* v___x_1713_, lean_object* v_as_1714_, lean_object* v_as_x27_1715_, lean_object* v_b_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_21091__boxed_1723_; lean_object* v_res_1724_; 
v___x_21091__boxed_1723_ = lean_unbox(v___x_1712_);
v_res_1724_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_21091__boxed_1723_, v___x_1713_, v_as_1714_, v_as_x27_1715_, v_b_1716_, v_a_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v_as_x27_1715_);
lean_dec(v_as_1714_);
lean_dec_ref(v___x_1713_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_1725_, lean_object* v_name_1726_, uint8_t v_bi_1727_, lean_object* v_type_1728_, lean_object* v_k_1729_, uint8_t v_kind_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1726_, v_bi_1727_, v_type_1728_, v_k_1729_, v_kind_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_name_1738_, lean_object* v_bi_1739_, lean_object* v_type_1740_, lean_object* v_k_1741_, lean_object* v_kind_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
uint8_t v_bi_boxed_1748_; uint8_t v_kind_boxed_1749_; lean_object* v_res_1750_; 
v_bi_boxed_1748_ = lean_unbox(v_bi_1739_);
v_kind_boxed_1749_ = lean_unbox(v_kind_1742_);
v_res_1750_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_1737_, v_name_1738_, v_bi_boxed_1748_, v_type_1740_, v_k_1741_, v_kind_boxed_1749_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_1751_, lean_object* v_name_1752_, lean_object* v_type_1753_, lean_object* v_k_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1752_, v_type_1753_, v_k_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_name_1762_, lean_object* v_type_1763_, lean_object* v_k_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_1761_, v_name_1762_, v_type_1763_, v_k_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14(lean_object* v_00_u03b1_1771_, lean_object* v_bs_1772_, lean_object* v_k_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___redArg(v_bs_1772_, v_k_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14___boxed(lean_object* v_00_u03b1_1780_, lean_object* v_bs_1781_, lean_object* v_k_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9_spec__14(v_00_u03b1_1780_, v_bs_1781_, v_k_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v_bs_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9(lean_object* v_00_u03b1_1789_, lean_object* v_bs_1790_, lean_object* v_k_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___redArg(v_bs_1790_, v_k_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_bs_1799_, lean_object* v_k_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__9(v_00_u03b1_1798_, v_bs_1799_, v_k_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_1807_, lean_object* v_constName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_constName_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_1815_, v_constName_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_1823_, lean_object* v_msg_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_msg_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_1831_, v_msg_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_1839_, lean_object* v_ref_1840_, lean_object* v_constName_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1840_, v_constName_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_ref_1849_, lean_object* v_constName_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_1848_, v_ref_1849_, v_constName_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v_ref_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16(lean_object* v_00_u03b1_1857_, lean_object* v_ref_1858_, lean_object* v_msg_1859_, lean_object* v_declHint_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___redArg(v_ref_1858_, v_msg_1859_, v_declHint_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_ref_1868_, lean_object* v_msg_1869_, lean_object* v_declHint_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16(v_00_u03b1_1867_, v_ref_1868_, v_msg_1869_, v_declHint_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_ref_1868_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21(lean_object* v_msg_1877_, lean_object* v_declHint_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___redArg(v_msg_1877_, v_declHint_1878_, v___y_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21___boxed(lean_object* v_msg_1885_, lean_object* v_declHint_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__20_spec__21(v_msg_1885_, v_declHint_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21(lean_object* v_00_u03b1_1893_, lean_object* v_ref_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___redArg(v_ref_1894_, v_msg_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21___boxed(lean_object* v_00_u03b1_1902_, lean_object* v_ref_1903_, lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__16_spec__21(v_00_u03b1_1902_, v_ref_1903_, v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v_ref_1903_);
return v_res_1910_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
