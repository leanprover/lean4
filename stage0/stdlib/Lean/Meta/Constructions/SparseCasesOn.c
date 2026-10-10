// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOn
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.Constructions.CtorIdx import Lean.Meta.HasNotBit import Lean.Meta.Transform
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkHasNotBit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SparseCasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 142, 211, 52, 27, 176, 89, 6)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 38, 184, 128, 76, 32, 215, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 79, 91, 86, 222, 171, 161, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 83, 47, 52, 170, 238, 223, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sparseCasesOnCacheExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 173, 73, 104, 127, 128, 171, 122)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
static const lean_array_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sparseCasesOnInfoExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 231, 162, 79, 58, 254, 239, 178)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Constructions.SparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.mkSparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "sparse `casesOn` for `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already registered as `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 140, 41, 106, 106, 114, 66, 206)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value;
static const lean_array_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "mkSparseCasesOn: unexpected number of parameters in type of `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkSparseCasesOn: constructor "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is not a constructor of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__0;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mkSparseCasesOn: unexpected number of universe parameters in `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__2;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__3;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_sparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 99, 43, 146, 60, 255, 155, 135)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__5_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "mkSparseCasesOn: requested casesOn combinator is not sparse"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__6 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_name_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_n_7_);
return v___x_10_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1_ = stack[0].m_obj;
lean_object* v_ys_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_1_, v_ys_2_, v_x_3_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object* v_xs_13_, lean_object* v_ys_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_13_, v_ys_14_, v_x_15_);
lean_dec_ref(v_ys_14_);
lean_dec_ref(v_xs_13_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_indName_20_; lean_object* v_ctors_21_; uint8_t v_isPrivate_22_; lean_object* v_indName_23_; lean_object* v_ctors_24_; uint8_t v_isPrivate_25_; uint8_t v___x_26_; 
v_indName_20_ = lean_ctor_get(v_x_18_, 0);
v_ctors_21_ = lean_ctor_get(v_x_18_, 1);
v_isPrivate_22_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*2);
v_indName_23_ = lean_ctor_get(v_x_19_, 0);
v_ctors_24_ = lean_ctor_get(v_x_19_, 1);
v_isPrivate_25_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*2);
v___x_26_ = lean_name_eq(v_indName_20_, v_indName_23_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = lean_array_get_size(v_ctors_21_);
v___x_28_ = lean_array_get_size(v_ctors_24_);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
return v___x_29_;
}
else
{
uint8_t v___x_30_; 
v___x_30_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_21_, v_ctors_24_, v___x_27_);
if (v___x_30_ == 0)
{
return v___x_30_;
}
else
{
if (v_isPrivate_25_ == 0)
{
if (v_isPrivate_22_ == 0)
{
return v___x_30_;
}
else
{
return v_isPrivate_25_;
}
}
else
{
return v_isPrivate_22_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_18_ = stack[0].m_obj;
lean_object* v_x_19_ = stack[1].m_obj;
uint8_t v_res_31_;
v_res_31_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_18_, v_x_19_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_32_, v_x_33_);
lean_dec_ref(v_x_33_);
lean_dec_ref(v_x_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object* v_xs_36_, lean_object* v_ys_37_, lean_object* v_hsz_38_, lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_36_, v_ys_37_, v_x_39_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_36_ = stack[0].m_obj;
lean_object* v_ys_37_ = stack[1].m_obj;
lean_object* v_x_39_ = stack[3].m_obj;
uint8_t v_res_42_;
v_res_42_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_36_, v_ys_37_, lean_box(0), v_x_39_, lean_box(0));
stack->m_num = v_res_42_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object* v_xs_43_, lean_object* v_ys_44_, lean_object* v_hsz_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_43_, v_ys_44_, v_hsz_45_, v_x_46_, v_x_47_);
lean_dec_ref(v_ys_44_);
lean_dec_ref(v_xs_43_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object* v_as_52_, size_t v_i_53_, size_t v_stop_54_, uint64_t v_b_55_){
_start:
{
uint64_t v___y_57_; uint8_t v___x_62_; 
v___x_62_ = lean_usize_dec_eq(v_i_53_, v_stop_54_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_array_uget_borrowed(v_as_52_, v_i_53_);
if (lean_obj_tag(v___x_63_) == 0)
{
uint64_t v___x_64_; 
v___x_64_ = 1723ULL;
v___y_57_ = v___x_64_;
goto v___jp_56_;
}
else
{
uint64_t v_hash_65_; 
v_hash_65_ = lean_ctor_get_uint64(v___x_63_, sizeof(void*)*2);
v___y_57_ = v_hash_65_;
goto v___jp_56_;
}
}
else
{
return v_b_55_;
}
v___jp_56_:
{
uint64_t v___x_58_; size_t v___x_59_; size_t v___x_60_; 
v___x_58_ = lean_uint64_mix_hash(v_b_55_, v___y_57_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_53_, v___x_59_);
v_i_53_ = v___x_60_;
v_b_55_ = v___x_58_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_52_ = stack[0].m_obj;
size_t v_i_53_ = stack[1].m_num;
size_t v_stop_54_ = stack[2].m_num;
uint64_t v_b_55_ = stack[3].m_num;
uint64_t v_res_66_;
v_res_66_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_52_, v_i_53_, v_stop_54_, v_b_55_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_, lean_object* v_b_70_){
_start:
{
size_t v_i_boxed_71_; size_t v_stop_boxed_72_; uint64_t v_b_boxed_73_; uint64_t v_res_74_; lean_object* v_r_75_; 
v_i_boxed_71_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_72_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_b_boxed_73_ = lean_unbox_uint64(v_b_70_);
lean_dec_ref(v_b_70_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_67_, v_i_boxed_71_, v_stop_boxed_72_, v_b_boxed_73_);
lean_dec_ref(v_as_67_);
v_r_75_ = lean_box_uint64(v_res_74_);
return v_r_75_;
}
}
uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object* v_x_76_){
_start:
{
lean_object* v_indName_77_; lean_object* v_ctors_78_; uint8_t v_isPrivate_79_; uint64_t v___y_81_; uint64_t v___y_82_; uint64_t v___x_88_; uint64_t v___y_90_; 
v_indName_77_ = lean_ctor_get(v_x_76_, 0);
v_ctors_78_ = lean_ctor_get(v_x_76_, 1);
v_isPrivate_79_ = lean_ctor_get_uint8(v_x_76_, sizeof(void*)*2);
v___x_88_ = 0ULL;
if (lean_obj_tag(v_indName_77_) == 0)
{
uint64_t v___x_99_; 
v___x_99_ = 1723ULL;
v___y_90_ = v___x_99_;
goto v___jp_89_;
}
else
{
uint64_t v_hash_100_; 
v_hash_100_ = lean_ctor_get_uint64(v_indName_77_, sizeof(void*)*2);
v___y_90_ = v_hash_100_;
goto v___jp_89_;
}
v___jp_80_:
{
uint64_t v___x_83_; 
v___x_83_ = lean_uint64_mix_hash(v___y_81_, v___y_82_);
if (v_isPrivate_79_ == 0)
{
uint64_t v___x_84_; uint64_t v___x_85_; 
v___x_84_ = 13ULL;
v___x_85_ = lean_uint64_mix_hash(v___x_83_, v___x_84_);
return v___x_85_;
}
else
{
uint64_t v___x_86_; uint64_t v___x_87_; 
v___x_86_ = 11ULL;
v___x_87_ = lean_uint64_mix_hash(v___x_83_, v___x_86_);
return v___x_87_;
}
}
v___jp_89_:
{
uint64_t v___x_91_; uint64_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_uint64_mix_hash(v___x_88_, v___y_90_);
v___x_92_ = 7ULL;
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_ctors_78_);
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
v___y_81_ = v___x_91_;
v___y_82_ = v___x_92_;
goto v___jp_80_;
}
else
{
size_t v___x_96_; size_t v___x_97_; uint64_t v___x_98_; 
v___x_96_ = ((size_t)0ULL);
v___x_97_ = lean_usize_of_nat(v___x_94_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_78_, v___x_96_, v___x_97_, v___x_92_);
v___y_81_ = v___x_91_;
v___y_82_ = v___x_98_;
goto v___jp_80_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_76_ = stack[0].m_obj;
uint64_t v_res_101_;
v_res_101_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_76_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object* v_x_102_){
_start:
{
uint64_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_102_);
lean_dec_ref(v_x_102_);
v_r_104_ = lean_box_uint64(v_res_103_);
return v_r_104_;
}
}
lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object* v___x_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_107_ = stack[0].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(v___x_107_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v___x_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(v___x_111_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_117_; lean_object* v___f_118_; 
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_118_, 0, v___x_117_);
return v___f_118_;
}
}
lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; 
v___f_153_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_box(1);
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_));
v___x_157_ = 0;
v___x_158_ = 1;
v___x_159_ = l_Lean_registerEnvExtension___redArg(v___f_153_, v___x_154_, v___x_155_, v___x_156_, v___x_157_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_160_;
v_res_160_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
return v_res_162_;
}
}
uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_171_, lean_object* v_n_172_, lean_object* v_x_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Environment_hasExposedBody(v_env_171_, v_n_172_);
return v___x_174_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_171_ = stack[0].m_obj;
lean_object* v_n_172_ = stack[1].m_obj;
lean_object* v_x_173_ = stack[2].m_obj;
uint8_t v_res_175_;
v_res_175_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(v_env_171_, v_n_172_, v_x_173_);
stack->m_num = v_res_175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_env_176_, lean_object* v_n_177_, lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(v_env_176_, v_n_177_, v_x_178_);
lean_dec_ref(v_x_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v_k_183_; lean_object* v_v_184_; lean_object* v_l_185_; lean_object* v_r_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_k_183_ = lean_ctor_get(v_x_182_, 1);
v_v_184_ = lean_ctor_get(v_x_182_, 2);
v_l_185_ = lean_ctor_get(v_x_182_, 3);
v_r_186_ = lean_ctor_get(v_x_182_, 4);
v___x_187_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_181_, v_l_185_);
lean_inc(v_v_184_);
lean_inc(v_k_183_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_k_183_);
lean_ctor_set(v___x_188_, 1, v_v_184_);
v___x_189_ = lean_array_push(v___x_187_, v___x_188_);
v_init_181_ = v___x_189_;
v_x_182_ = v_r_186_;
goto _start;
}
else
{
return v_init_181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_191_, v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_196_, lean_object* v_s_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v_all_200_; lean_object* v___x_201_; lean_object* v_exported_202_; lean_object* v___x_203_; 
v___f_198_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_198_, 0, v_env_196_);
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v_all_200_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_199_, v_s_197_);
v___x_201_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_198_, v_s_197_);
v_exported_202_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_199_, v___x_201_);
lean_dec(v___x_201_);
lean_inc_ref(v_exported_202_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v_exported_202_);
lean_ctor_set(v___x_203_, 1, v_exported_202_);
lean_ctor_set(v___x_203_, 2, v_all_200_);
return v___x_203_;
}
}
lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; 
v___f_212_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_215_ = 0;
v___x_216_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_213_, v___x_214_, v___x_215_, v___f_212_);
return v___x_216_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_217_;
v_res_217_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object* v_init_220_, lean_object* v_t_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_220_, v_t_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_223_, lean_object* v_t_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(v_init_223_, v_t_224_);
lean_dec(v_t_224_);
return v_res_225_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object* v_kind_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_auxDeclNGen_230_; lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; lean_object* v_env_237_; lean_object* v_nextMacroScope_238_; lean_object* v_ngen_239_; lean_object* v_traceState_240_; lean_object* v_cache_241_; lean_object* v_recordedDeps_242_; lean_object* v_messages_243_; lean_object* v_infoState_244_; lean_object* v_snapshotTasks_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_254_; 
v___x_229_ = lean_st_ref_get(v___y_227_);
v_auxDeclNGen_230_ = lean_ctor_get(v___x_229_, 3);
lean_inc_ref(v_auxDeclNGen_230_);
lean_dec(v___x_229_);
v___x_231_ = lean_st_ref_get(v___y_227_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_232_, v_auxDeclNGen_230_, v_kind_226_);
v_fst_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v___x_233_);
v___x_236_ = lean_st_ref_take(v___y_227_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
v_nextMacroScope_238_ = lean_ctor_get(v___x_236_, 1);
v_ngen_239_ = lean_ctor_get(v___x_236_, 2);
v_traceState_240_ = lean_ctor_get(v___x_236_, 4);
v_cache_241_ = lean_ctor_get(v___x_236_, 5);
v_recordedDeps_242_ = lean_ctor_get(v___x_236_, 6);
v_messages_243_ = lean_ctor_get(v___x_236_, 7);
v_infoState_244_ = lean_ctor_get(v___x_236_, 8);
v_snapshotTasks_245_ = lean_ctor_get(v___x_236_, 9);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_236_, 3);
lean_dec(v_unused_255_);
v___x_247_ = v___x_236_;
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snapshotTasks_245_);
lean_inc(v_infoState_244_);
lean_inc(v_messages_243_);
lean_inc(v_recordedDeps_242_);
lean_inc(v_cache_241_);
lean_inc(v_traceState_240_);
lean_inc(v_ngen_239_);
lean_inc(v_nextMacroScope_238_);
lean_inc(v_env_237_);
lean_dec(v___x_236_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 3, v_snd_235_);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_env_237_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_nextMacroScope_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_ngen_239_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_snd_235_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_traceState_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 5, v_cache_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 6, v_recordedDeps_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 7, v_messages_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 8, v_infoState_244_);
lean_ctor_set(v_reuseFailAlloc_253_, 9, v_snapshotTasks_245_);
v___x_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_st_ref_put(v___y_227_, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_fst_234_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_226_ = stack[0].m_obj;
lean_object* v___y_227_ = stack[1].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_226_, v___y_227_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object* v_kind_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_257_, v___y_258_);
lean_dec(v___y_258_);
return v_res_260_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object* v_kind_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_261_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_261_ = stack[0].m_obj;
lean_object* v___y_262_ = stack[1].m_obj;
lean_object* v___y_263_ = stack[2].m_obj;
lean_object* v___y_264_ = stack[3].m_obj;
lean_object* v___y_265_ = stack[4].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object* v_kind_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_s_276_, lean_object* v_msg_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_panic_fn_borrowed(v_s_276_, v_msg_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_s_279_, lean_object* v_msg_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_s_279_, v_msg_280_);
lean_dec_ref(v_s_279_);
return v_res_281_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v_c_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
v___x_290_ = lean_apply_7(v_k_282_, v_b_283_, v_c_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_282_ = stack[0].m_obj;
lean_object* v_b_283_ = stack[1].m_obj;
lean_object* v_c_284_ = stack[2].m_obj;
lean_object* v___y_285_ = stack[3].m_obj;
lean_object* v___y_286_ = stack[4].m_obj;
lean_object* v___y_287_ = stack[5].m_obj;
lean_object* v___y_288_ = stack[6].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(v_k_282_, v_b_283_, v_c_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object* v_k_292_, lean_object* v_b_293_, lean_object* v_c_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(v_k_292_, v_b_293_, v_c_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object* v_type_301_, lean_object* v_k_302_, uint8_t v_cleanupAnnotations_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___f_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_309_, 0, v_k_302_);
v___x_310_ = 0;
v___x_311_ = lean_box(0);
v___x_312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_310_, v___x_311_, v_type_301_, v___f_309_, v_cleanupAnnotations_303_, v___x_310_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_312_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_312_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_301_ = stack[0].m_obj;
lean_object* v_k_302_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_303_ = stack[2].m_num;
lean_object* v___y_304_ = stack[3].m_obj;
lean_object* v___y_305_ = stack[4].m_obj;
lean_object* v___y_306_ = stack[5].m_obj;
lean_object* v___y_307_ = stack[6].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_301_, v_k_302_, v_cleanupAnnotations_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object* v_type_330_, lean_object* v_k_331_, lean_object* v_cleanupAnnotations_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_338_; lean_object* v_res_339_; 
v_cleanupAnnotations_boxed_338_ = lean_unbox(v_cleanupAnnotations_332_);
v_res_339_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_330_, v_k_331_, v_cleanupAnnotations_boxed_338_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_339_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_00_u03b1_340_, lean_object* v_type_341_, lean_object* v_k_342_, uint8_t v_cleanupAnnotations_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_341_, v_k_342_, v_cleanupAnnotations_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_341_ = stack[1].m_obj;
lean_object* v_k_342_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_343_ = stack[3].m_num;
lean_object* v___y_344_ = stack[4].m_obj;
lean_object* v___y_345_ = stack[5].m_obj;
lean_object* v___y_346_ = stack[6].m_obj;
lean_object* v___y_347_ = stack[7].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_box(0), v_type_341_, v_k_342_, v_cleanupAnnotations_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_00_u03b1_351_, lean_object* v_type_352_, lean_object* v_k_353_, lean_object* v_cleanupAnnotations_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_360_; lean_object* v_res_361_; 
v_cleanupAnnotations_boxed_360_ = lean_unbox(v_cleanupAnnotations_354_);
v_res_361_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_00_u03b1_351_, v_type_352_, v_k_353_, v_cleanupAnnotations_boxed_360_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_361_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object* v_name_362_, lean_object* v_levelParams_363_, lean_object* v_type_364_, lean_object* v_value_365_, lean_object* v_hints_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; uint8_t v___y_371_; uint8_t v___y_378_; lean_object* v_env_381_; uint8_t v___x_382_; 
v___x_369_ = lean_st_ref_get(v___y_367_);
v_env_381_ = lean_ctor_get(v___x_369_, 0);
lean_inc_ref_n(v_env_381_, 2);
lean_dec(v___x_369_);
v___x_382_ = l_Lean_Environment_hasUnsafe(v_env_381_, v_type_364_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = l_Lean_Environment_hasUnsafe(v_env_381_, v_value_365_);
v___y_378_ = v___x_383_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_env_381_);
v___y_378_ = v___x_382_;
goto v___jp_377_;
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_inc(v_name_362_);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v_name_362_);
lean_ctor_set(v___x_372_, 1, v_levelParams_363_);
lean_ctor_set(v___x_372_, 2, v_type_364_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v_name_362_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_375_, 0, v___x_372_);
lean_ctor_set(v___x_375_, 1, v_value_365_);
lean_ctor_set(v___x_375_, 2, v_hints_366_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*4, v___y_371_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
v___jp_377_:
{
if (v___y_378_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 1;
v___y_371_ = v___x_379_;
goto v___jp_370_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
v___y_371_ = v___x_380_;
goto v___jp_370_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_362_ = stack[0].m_obj;
lean_object* v_levelParams_363_ = stack[1].m_obj;
lean_object* v_type_364_ = stack[2].m_obj;
lean_object* v_value_365_ = stack[3].m_obj;
lean_object* v_hints_366_ = stack[4].m_obj;
lean_object* v___y_367_ = stack[5].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_362_, v_levelParams_363_, v_type_364_, v_value_365_, v_hints_366_, v___y_367_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object* v_name_385_, lean_object* v_levelParams_386_, lean_object* v_type_387_, lean_object* v_value_388_, lean_object* v_hints_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_385_, v_levelParams_386_, v_type_387_, v_value_388_, v_hints_389_, v___y_390_);
lean_dec(v___y_390_);
return v_res_392_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_name_393_, lean_object* v_levelParams_394_, lean_object* v_type_395_, lean_object* v_value_396_, lean_object* v_hints_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_393_, v_levelParams_394_, v_type_395_, v_value_396_, v_hints_397_, v___y_401_);
return v___x_403_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_393_ = stack[0].m_obj;
lean_object* v_levelParams_394_ = stack[1].m_obj;
lean_object* v_type_395_ = stack[2].m_obj;
lean_object* v_value_396_ = stack[3].m_obj;
lean_object* v_hints_397_ = stack[4].m_obj;
lean_object* v___y_398_ = stack[5].m_obj;
lean_object* v___y_399_ = stack[6].m_obj;
lean_object* v___y_400_ = stack[7].m_obj;
lean_object* v___y_401_ = stack[8].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_name_393_, v_levelParams_394_, v_type_395_, v_value_396_, v_hints_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_name_405_, lean_object* v_levelParams_406_, lean_object* v_type_407_, lean_object* v_value_408_, lean_object* v_hints_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_name_405_, v_levelParams_406_, v_type_407_, v_value_408_, v_hints_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___f_423_; lean_object* v___x_17664__overap_424_; lean_object* v___x_425_; 
v___f_423_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0));
v___x_17664__overap_424_ = lean_panic_fn_borrowed(v___f_423_, v_msg_417_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
v___x_425_ = lean_apply_5(v___x_17664__overap_424_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, lean_box(0));
return v___x_425_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_417_ = stack[0].m_obj;
lean_object* v___y_418_ = stack[1].m_obj;
lean_object* v___y_419_ = stack[2].m_obj;
lean_object* v___y_420_ = stack[3].m_obj;
lean_object* v___y_421_ = stack[4].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_ks_438_; lean_object* v_vs_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_463_; 
v_ks_438_ = lean_ctor_get(v_x_434_, 0);
v_vs_439_ = lean_ctor_get(v_x_434_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_463_ == 0)
{
v___x_441_ = v_x_434_;
v_isShared_442_ = v_isSharedCheck_463_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_vs_439_);
lean_inc(v_ks_438_);
lean_dec(v_x_434_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_463_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_array_get_size(v_ks_438_);
v___x_444_ = lean_nat_dec_lt(v_x_435_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec(v_x_435_);
v___x_445_ = lean_array_push(v_ks_438_, v_x_436_);
v___x_446_ = lean_array_push(v_vs_439_, v_x_437_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_446_);
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
lean_object* v_k_x27_450_; uint8_t v___x_451_; 
v_k_x27_450_ = lean_array_fget_borrowed(v_ks_438_, v_x_435_);
v___x_451_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_436_, v_k_x27_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_453_; 
if (v_isShared_442_ == 0)
{
v___x_453_ = v___x_441_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_ks_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_vs_439_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_x_435_, v___x_454_);
lean_dec(v_x_435_);
v_x_434_ = v___x_453_;
v_x_435_ = v___x_455_;
goto _start;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_array_fset(v_ks_438_, v_x_435_, v_x_436_);
v___x_459_ = lean_array_fset(v_vs_439_, v_x_435_, v_x_437_);
lean_dec(v_x_435_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_459_);
lean_ctor_set(v___x_441_, 0, v___x_458_);
v___x_461_ = v___x_441_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object* v_n_464_, lean_object* v_k_465_, lean_object* v_v_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_n_464_, v___x_467_, v_k_465_, v_v_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_469_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object* v_x_470_, size_t v_x_471_, size_t v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_es_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v_j_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_es_475_ = lean_ctor_get(v_x_470_, 0);
v___x_476_ = ((size_t)31ULL);
v___x_477_ = lean_usize_land(v_x_471_, v___x_476_);
v_j_478_ = lean_usize_to_nat(v___x_477_);
v___x_479_ = lean_array_get_size(v_es_475_);
v___x_480_ = lean_nat_dec_lt(v_j_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_dec(v_j_478_);
lean_dec(v_x_474_);
lean_dec_ref(v_x_473_);
return v_x_470_;
}
else
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_519_; 
lean_inc_ref(v_es_475_);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_x_470_, 0);
lean_dec(v_unused_520_);
v___x_482_ = v_x_470_;
v_isShared_483_ = v_isSharedCheck_519_;
goto v_resetjp_481_;
}
else
{
lean_dec(v_x_470_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_519_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_v_484_; lean_object* v___x_485_; lean_object* v_xs_x27_486_; lean_object* v___y_488_; 
v_v_484_ = lean_array_fget(v_es_475_, v_j_478_);
v___x_485_ = lean_box(0);
v_xs_x27_486_ = lean_array_fset(v_es_475_, v_j_478_, v___x_485_);
switch(lean_obj_tag(v_v_484_))
{
case 0:
{
lean_object* v_key_493_; lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_504_; 
v_key_493_ = lean_ctor_get(v_v_484_, 0);
v_val_494_ = lean_ctor_get(v_v_484_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_v_484_);
if (v_isSharedCheck_504_ == 0)
{
v___x_496_ = v_v_484_;
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_inc(v_key_493_);
lean_dec(v_v_484_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; 
v___x_498_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_473_, v_key_493_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_del_object(v___x_496_);
v___x_499_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_493_, v_val_494_, v_x_473_, v_x_474_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___y_488_ = v___x_500_;
goto v___jp_487_;
}
else
{
lean_object* v___x_502_; 
lean_dec(v_val_494_);
lean_dec(v_key_493_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_x_474_);
lean_ctor_set(v___x_496_, 0, v_x_473_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_x_473_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_x_474_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v___y_488_ = v___x_502_;
goto v___jp_487_;
}
}
}
}
case 1:
{
lean_object* v_node_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_517_; 
v_node_505_ = lean_ctor_get(v_v_484_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_v_484_);
if (v_isSharedCheck_517_ == 0)
{
v___x_507_ = v_v_484_;
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_node_505_);
lean_dec(v_v_484_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_509_ = ((size_t)5ULL);
v___x_510_ = lean_usize_shift_right(v_x_471_, v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_x_472_, v___x_511_);
v___x_513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_505_, v___x_510_, v___x_512_, v_x_473_, v_x_474_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_513_);
v___x_515_ = v___x_507_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_488_ = v___x_515_;
goto v___jp_487_;
}
}
}
default: 
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_x_473_);
lean_ctor_set(v___x_518_, 1, v_x_474_);
v___y_488_ = v___x_518_;
goto v___jp_487_;
}
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_array_fset(v_xs_x27_486_, v_j_478_, v___y_488_);
lean_dec(v_j_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_489_);
v___x_491_ = v___x_482_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_object* v_ks_521_; lean_object* v_vs_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_540_; 
v_ks_521_ = lean_ctor_get(v_x_470_, 0);
v_vs_522_ = lean_ctor_get(v_x_470_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_540_ == 0)
{
v___x_524_ = v_x_470_;
v_isShared_525_ = v_isSharedCheck_540_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_vs_522_);
lean_inc(v_ks_521_);
lean_dec(v_x_470_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_540_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_ks_521_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_vs_522_);
v___x_527_ = v_reuseFailAlloc_539_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v_newNode_528_; size_t v___x_529_; uint8_t v___x_530_; 
v_newNode_528_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v___x_527_, v_x_473_, v_x_474_);
v___x_529_ = ((size_t)7ULL);
v___x_530_ = lean_usize_dec_le(v___x_529_, v_x_472_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_528_);
v___x_532_ = lean_unsigned_to_nat(4u);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
if (v___x_533_ == 0)
{
lean_object* v_ks_534_; lean_object* v_vs_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_ks_534_ = lean_ctor_get(v_newNode_528_, 0);
lean_inc_ref(v_ks_534_);
v_vs_535_ = lean_ctor_get(v_newNode_528_, 1);
lean_inc_ref(v_vs_535_);
lean_dec_ref(v_newNode_528_);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
v___x_538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_x_472_, v_ks_534_, v_vs_535_, v___x_536_, v___x_537_);
lean_dec_ref(v_vs_535_);
lean_dec_ref(v_ks_534_);
return v___x_538_;
}
else
{
return v_newNode_528_;
}
}
else
{
return v_newNode_528_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_470_ = stack[0].m_obj;
size_t v_x_471_ = stack[1].m_num;
size_t v_x_472_ = stack[2].m_num;
lean_object* v_x_473_ = stack[3].m_obj;
lean_object* v_x_474_ = stack[4].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_470_, v_x_471_, v_x_472_, v_x_473_, v_x_474_);
stack->m_obj
 = v_res_541_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t v_depth_542_, lean_object* v_keys_543_, lean_object* v_vals_544_, lean_object* v_i_545_, lean_object* v_entries_546_){
_start:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_keys_543_);
v___x_548_ = lean_nat_dec_lt(v_i_545_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_i_545_);
return v_entries_546_;
}
else
{
lean_object* v_k_549_; lean_object* v_v_550_; uint64_t v___x_551_; size_t v_h_552_; size_t v___x_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v_h_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_k_549_ = lean_array_fget_borrowed(v_keys_543_, v_i_545_);
v_v_550_ = lean_array_fget_borrowed(v_vals_544_, v_i_545_);
v___x_551_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_549_);
v_h_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = ((size_t)5ULL);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v_depth_542_, v___x_555_);
v___x_557_ = lean_usize_mul(v___x_553_, v___x_556_);
v_h_558_ = lean_usize_shift_right(v_h_552_, v___x_557_);
v___x_559_ = lean_nat_add(v_i_545_, v___x_554_);
lean_dec(v_i_545_);
lean_inc(v_v_550_);
lean_inc(v_k_549_);
v___x_560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_546_, v_h_558_, v_depth_542_, v_k_549_, v_v_550_);
v_i_545_ = v___x_559_;
v_entries_546_ = v___x_560_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_542_ = stack[0].m_num;
lean_object* v_keys_543_ = stack[1].m_obj;
lean_object* v_vals_544_ = stack[2].m_obj;
lean_object* v_i_545_ = stack[3].m_obj;
lean_object* v_entries_546_ = stack[4].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_542_, v_keys_543_, v_vals_544_, v_i_545_, v_entries_546_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object* v_depth_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_entries_567_){
_start:
{
size_t v_depth_boxed_568_; lean_object* v_res_569_; 
v_depth_boxed_568_ = lean_unbox_usize(v_depth_563_);
lean_dec(v_depth_563_);
v_res_569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_boxed_568_, v_keys_564_, v_vals_565_, v_i_566_, v_entries_567_);
lean_dec_ref(v_vals_565_);
lean_dec_ref(v_keys_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v_x_22060__boxed_575_; size_t v_x_22061__boxed_576_; lean_object* v_res_577_; 
v_x_22060__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_x_22061__boxed_576_ = lean_unbox_usize(v_x_572_);
lean_dec(v_x_572_);
v_res_577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_570_, v_x_22060__boxed_575_, v_x_22061__boxed_576_, v_x_573_, v_x_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
uint64_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_581_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_579_);
v___x_582_ = lean_uint64_to_usize(v___x_581_);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_578_, v___x_582_, v___x_583_, v_x_579_, v_x_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object* v_keys_585_, lean_object* v_vals_586_, lean_object* v_i_587_, lean_object* v_k_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_array_get_size(v_keys_585_);
v___x_590_ = lean_nat_dec_lt(v_i_587_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v_i_587_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v_k_x27_592_; uint8_t v___x_593_; 
v_k_x27_592_ = lean_array_fget_borrowed(v_keys_585_, v_i_587_);
v___x_593_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_588_, v_k_x27_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_i_587_, v___x_594_);
lean_dec(v_i_587_);
v_i_587_ = v___x_595_;
goto _start;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_array_fget_borrowed(v_vals_586_, v_i_587_);
lean_dec(v_i_587_);
lean_inc(v___x_597_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_keys_599_, lean_object* v_vals_600_, lean_object* v_i_601_, lean_object* v_k_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_599_, v_vals_600_, v_i_601_, v_k_602_);
lean_dec_ref(v_k_602_);
lean_dec_ref(v_vals_600_);
lean_dec_ref(v_keys_599_);
return v_res_603_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_604_, size_t v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v_es_607_; lean_object* v___x_608_; size_t v___x_609_; size_t v___x_610_; lean_object* v_j_611_; lean_object* v___x_612_; 
v_es_607_ = lean_ctor_get(v_x_604_, 0);
v___x_608_ = lean_box(2);
v___x_609_ = ((size_t)31ULL);
v___x_610_ = lean_usize_land(v_x_605_, v___x_609_);
v_j_611_ = lean_usize_to_nat(v___x_610_);
v___x_612_ = lean_array_get_borrowed(v___x_608_, v_es_607_, v_j_611_);
lean_dec(v_j_611_);
switch(lean_obj_tag(v___x_612_))
{
case 0:
{
lean_object* v_key_613_; lean_object* v_val_614_; uint8_t v___x_615_; 
v_key_613_ = lean_ctor_get(v___x_612_, 0);
v_val_614_ = lean_ctor_get(v___x_612_, 1);
v___x_615_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_606_, v_key_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
lean_inc(v_val_614_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_val_614_);
return v___x_617_;
}
}
case 1:
{
lean_object* v_node_618_; size_t v___x_619_; size_t v___x_620_; 
v_node_618_ = lean_ctor_get(v___x_612_, 0);
v___x_619_ = ((size_t)5ULL);
v___x_620_ = lean_usize_shift_right(v_x_605_, v___x_619_);
v_x_604_ = v_node_618_;
v_x_605_ = v___x_620_;
goto _start;
}
default: 
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
}
else
{
lean_object* v_ks_623_; lean_object* v_vs_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_ks_623_ = lean_ctor_get(v_x_604_, 0);
v_vs_624_ = lean_ctor_get(v_x_604_, 1);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_ks_623_, v_vs_624_, v___x_625_, v_x_606_);
return v___x_626_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_604_ = stack[0].m_obj;
size_t v_x_605_ = stack[1].m_num;
lean_object* v_x_606_ = stack[2].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_604_, v_x_605_, v_x_606_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
size_t v_x_22344__boxed_631_; lean_object* v_res_632_; 
v_x_22344__boxed_631_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_res_632_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_628_, v_x_22344__boxed_631_, v_x_630_);
lean_dec_ref(v_x_630_);
lean_dec_ref(v_x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
uint64_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; 
v___x_635_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_634_);
v___x_636_ = lean_uint64_to_usize(v___x_635_);
v___x_637_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_633_, v___x_636_, v_x_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_638_, v_x_639_);
lean_dec_ref(v_x_639_);
lean_dec_ref(v_x_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object* v___x_646_, lean_object* v_a_647_, lean_object* v_s_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_s_648_, v___x_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_s_648_, v___x_646_, v_a_647_);
return v___x_650_;
}
else
{
lean_object* v_val_651_; uint8_t v___x_652_; 
lean_dec_ref(v___x_646_);
v_val_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_649_, 1);
v___x_652_ = lean_name_eq(v_val_651_, v_a_647_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_653_ = 1;
v___x_654_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_655_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_656_ = lean_unsigned_to_nat(144u);
v___x_657_ = lean_unsigned_to_nat(8u);
v___x_658_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2));
v___x_659_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_647_, v___x_653_);
v___x_660_ = lean_string_append(v___x_658_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_651_, v___x_653_);
v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_666_ = lean_string_append(v___x_664_, v___x_665_);
v___x_667_ = l_mkPanicMessageWithDecl(v___x_654_, v___x_655_, v___x_656_, v___x_657_, v___x_666_);
lean_dec_ref(v___x_666_);
v___x_668_ = lean_panic_fn_borrowed(v_s_648_, v___x_667_);
lean_dec_ref(v_s_648_);
return v___x_668_;
}
else
{
lean_dec(v_val_651_);
lean_dec(v_a_647_);
return v_s_648_;
}
}
}
}
lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, uint8_t v___x_672_, lean_object* v_h_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; 
v___x_679_ = lean_array_push(v___x_669_, v_h_673_);
v___x_680_ = l_Lean_mkAppN(v___x_670_, v___x_671_);
v___x_681_ = 1;
v___x_682_ = 1;
v___x_683_ = l_Lean_Meta_mkForallFVars(v___x_679_, v___x_680_, v___x_672_, v___x_681_, v___x_681_, v___x_682_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec_ref(v___x_679_);
return v___x_683_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkSparseCasesOn___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_669_ = stack[0].m_obj;
lean_object* v___x_670_ = stack[1].m_obj;
lean_object* v___x_671_ = stack[2].m_obj;
uint8_t v___x_672_ = stack[3].m_num;
lean_object* v_h_673_ = stack[4].m_obj;
lean_object* v___y_674_ = stack[5].m_obj;
lean_object* v___y_675_ = stack[6].m_obj;
lean_object* v___y_676_ = stack[7].m_obj;
lean_object* v___y_677_ = stack[8].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_669_, v___x_670_, v___x_671_, v___x_672_, v_h_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v_h_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_22524__boxed_695_; lean_object* v_res_696_; 
v___x_22524__boxed_695_ = lean_unbox(v___x_688_);
v_res_696_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_685_, v___x_686_, v___x_687_, v___x_22524__boxed_695_, v_h_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v___x_687_);
return v_res_696_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object* v_msgData_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_env_704_; uint8_t v___x_705_; lean_object* v_env_706_; lean_object* v___x_707_; lean_object* v_toCold_708_; lean_object* v_mctx_709_; lean_object* v_lctx_710_; lean_object* v_options_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_703_ = lean_st_ref_get(v___y_701_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_ref(v_env_704_);
lean_dec(v___x_703_);
v___x_705_ = 0;
v_env_706_ = l_Lean_Environment_setRecordingDeps(v_env_704_, v___x_705_);
v___x_707_ = lean_st_ref_get(v___y_699_);
v_toCold_708_ = lean_ctor_get(v___y_700_, 0);
v_mctx_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_mctx_709_);
lean_dec(v___x_707_);
v_lctx_710_ = lean_ctor_get(v___y_698_, 2);
v_options_711_ = lean_ctor_get(v_toCold_708_, 2);
lean_inc_ref(v_options_711_);
lean_inc_ref(v_lctx_710_);
v___x_712_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_712_, 0, v_env_706_);
lean_ctor_set(v___x_712_, 1, v_mctx_709_);
lean_ctor_set(v___x_712_, 2, v_lctx_710_);
lean_ctor_set(v___x_712_, 3, v_options_711_);
v___x_713_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v_msgData_697_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_697_ = stack[0].m_obj;
lean_object* v___y_698_ = stack[1].m_obj;
lean_object* v___y_699_ = stack[2].m_obj;
lean_object* v___y_700_ = stack[3].m_obj;
lean_object* v___y_701_ = stack[4].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msgData_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msgData_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_ref_729_; lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_ref_729_ = lean_ctor_get(v___y_726_, 2);
v___x_730_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_ref_729_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_ref_729_);
lean_ctor_set(v___x_735_, 1, v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_723_ = stack[0].m_obj;
lean_object* v___y_724_ = stack[1].m_obj;
lean_object* v___y_725_ = stack[2].m_obj;
lean_object* v___y_726_ = stack[3].m_obj;
lean_object* v___y_727_ = stack[4].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_instMonadEIO___redArg();
return v___x_748_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_toApplicative_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_822_; 
v___x_759_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
v___x_760_ = l_StateRefT_x27_instMonad___redArg(v___x_759_);
v_toApplicative_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_760_, 1);
lean_dec(v_unused_823_);
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_822_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_toApplicative_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_822_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_toFunctor_765_; lean_object* v_toSeq_766_; lean_object* v_toSeqLeft_767_; lean_object* v_toSeqRight_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_820_; 
v_toFunctor_765_ = lean_ctor_get(v_toApplicative_761_, 0);
v_toSeq_766_ = lean_ctor_get(v_toApplicative_761_, 2);
v_toSeqLeft_767_ = lean_ctor_get(v_toApplicative_761_, 3);
v_toSeqRight_768_ = lean_ctor_get(v_toApplicative_761_, 4);
v_isSharedCheck_820_ = !lean_is_exclusive(v_toApplicative_761_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_dec(v_unused_821_);
v___x_770_ = v_toApplicative_761_;
v_isShared_771_ = v_isSharedCheck_820_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_toSeqRight_768_);
lean_inc(v_toSeqLeft_767_);
lean_inc(v_toSeq_766_);
lean_inc(v_toFunctor_765_);
lean_dec(v_toApplicative_761_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_820_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_781_; 
v___f_772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1));
v___f_773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_765_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_774_, 0, v_toFunctor_765_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_775_, 0, v_toFunctor_765_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___f_774_);
lean_ctor_set(v___x_776_, 1, v___f_775_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeqRight_768_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeqLeft_767_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeq_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 4, v___f_777_);
lean_ctor_set(v___x_770_, 3, v___f_778_);
lean_ctor_set(v___x_770_, 2, v___f_779_);
lean_ctor_set(v___x_770_, 1, v___f_772_);
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___f_772_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v___f_779_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v___f_777_);
v___x_781_ = v_reuseFailAlloc_819_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___f_773_);
lean_ctor_set(v___x_763_, 0, v___x_781_);
v___x_783_ = v___x_763_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_773_);
v___x_783_ = v_reuseFailAlloc_818_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v_toApplicative_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_816_; 
v___x_784_ = l_StateRefT_x27_instMonad___redArg(v___x_783_);
v_toApplicative_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_784_, 1);
lean_dec(v_unused_817_);
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_816_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_toApplicative_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_816_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_toFunctor_789_; lean_object* v_toSeq_790_; lean_object* v_toSeqLeft_791_; lean_object* v_toSeqRight_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_814_; 
v_toFunctor_789_ = lean_ctor_get(v_toApplicative_785_, 0);
v_toSeq_790_ = lean_ctor_get(v_toApplicative_785_, 2);
v_toSeqLeft_791_ = lean_ctor_get(v_toApplicative_785_, 3);
v_toSeqRight_792_ = lean_ctor_get(v_toApplicative_785_, 4);
v_isSharedCheck_814_ = !lean_is_exclusive(v_toApplicative_785_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_toApplicative_785_, 1);
lean_dec(v_unused_815_);
v___x_794_ = v_toApplicative_785_;
v_isShared_795_ = v_isSharedCheck_814_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_toSeqRight_792_);
lean_inc(v_toSeqLeft_791_);
lean_inc(v_toSeq_790_);
lean_inc(v_toFunctor_789_);
lean_dec(v_toApplicative_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_814_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_805_; 
v___f_796_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3));
v___f_797_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_789_);
v___f_798_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_798_, 0, v_toFunctor_789_);
v___f_799_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_799_, 0, v_toFunctor_789_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___f_798_);
lean_ctor_set(v___x_800_, 1, v___f_799_);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_801_, 0, v_toSeqRight_792_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_802_, 0, v_toSeqLeft_791_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_803_, 0, v_toSeq_790_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 4, v___f_801_);
lean_ctor_set(v___x_794_, 3, v___f_802_);
lean_ctor_set(v___x_794_, 2, v___f_803_);
lean_ctor_set(v___x_794_, 1, v___f_796_);
lean_ctor_set(v___x_794_, 0, v___x_800_);
v___x_805_ = v___x_794_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___f_796_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v___f_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v___f_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v___f_801_);
v___x_805_ = v_reuseFailAlloc_813_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___f_797_);
lean_ctor_set(v___x_787_, 0, v___x_805_);
v___x_807_ = v___x_787_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___f_797_);
v___x_807_ = v_reuseFailAlloc_812_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_17943__overap_810_; lean_object* v___x_811_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_instInhabitedOfMonad___redArg(v___x_807_, v___x_808_);
v___x_17943__overap_810_ = lean_panic_fn_borrowed(v___x_809_, v_msg_753_);
lean_dec(v___x_809_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
v___x_811_ = lean_apply_5(v___x_17943__overap_810_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, lean_box(0));
return v___x_811_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_753_ = stack[0].m_obj;
lean_object* v___y_754_ = stack[1].m_obj;
lean_object* v___y_755_ = stack[2].m_obj;
lean_object* v___y_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_841_ = lean_unsigned_to_nat(11u);
v___x_842_ = lean_unsigned_to_nat(122u);
v___x_843_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_844_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3));
v___x_845_ = l_mkPanicMessageWithDecl(v___x_844_, v___x_843_, v___x_842_, v___x_841_, v___x_840_);
return v___x_845_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_860_; lean_object* v_env_861_; uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_860_ = lean_st_ref_get(v___y_850_);
v_env_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_env_861_);
lean_dec(v___x_860_);
v___x_862_ = 0;
lean_inc(v_constName_846_);
v___x_863_ = l_Lean_Environment_findAsync_x3f(v_env_861_, v_constName_846_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v_val_864_; uint8_t v_kind_865_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_863_, 1);
v_kind_865_ = lean_ctor_get_uint8(v_val_864_, sizeof(void*)*3);
if (v_kind_865_ == 6)
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_864_);
if (lean_obj_tag(v___x_866_) == 6)
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_constName_846_);
v_val_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 0);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_val_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___x_866_);
v___x_875_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6);
v___x_876_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_875_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_885_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_885_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 0)
{
lean_del_object(v___x_879_);
goto v___jp_852_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; 
lean_dec(v_constName_846_);
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_877_, 1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_val_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_constName_846_);
v_a_886_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_876_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_876_);
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
}
}
else
{
lean_dec(v_val_864_);
goto v___jp_852_;
}
}
else
{
lean_dec(v___x_863_);
goto v___jp_852_;
}
v___jp_852_:
{
lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_853_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_854_ = 0;
v___x_855_ = l_Lean_MessageData_ofConstName(v_constName_846_, v___x_854_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_853_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_858_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
return v___x_859_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_846_ = stack[0].m_obj;
lean_object* v___y_847_ = stack[1].m_obj;
lean_object* v___y_848_ = stack[2].m_obj;
lean_object* v___y_849_ = stack[3].m_obj;
lean_object* v___y_850_ = stack[4].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object* v_xs_902_, lean_object* v_v_903_, lean_object* v_i_904_){
_start:
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_array_get_size(v_xs_902_);
v___x_906_ = lean_nat_dec_lt(v_i_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_i_904_);
v___x_907_ = lean_box(0);
return v___x_907_;
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_array_fget_borrowed(v_xs_902_, v_i_904_);
v___x_909_ = lean_name_eq(v___x_908_, v_v_903_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v_i_904_, v___x_910_);
lean_dec(v_i_904_);
v_i_904_ = v___x_911_;
goto _start;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v_i_904_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object* v_xs_914_, lean_object* v_v_915_, lean_object* v_i_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_914_, v_v_915_, v_i_916_);
lean_dec(v_v_915_);
lean_dec_ref(v_xs_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object* v_xs_918_, lean_object* v_v_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_918_, v_v_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object* v_xs_922_, lean_object* v_v_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_922_, v_v_923_);
lean_dec(v_v_923_);
lean_dec_ref(v_xs_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object* v_xs_925_, lean_object* v_v_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_925_, v_v_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_928_; 
v___x_928_ = lean_box(0);
return v___x_928_;
}
else
{
lean_object* v_val_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_val_929_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_927_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_val_929_);
lean_dec(v___x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_val_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object* v_xs_937_, lean_object* v_v_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_xs_937_, v_v_938_);
lean_dec(v_v_938_);
lean_dec_ref(v_xs_937_);
return v_res_939_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object* v_ctors_940_, lean_object* v_a_941_, lean_object* v___x_942_, lean_object* v_a_943_, uint8_t v___x_944_, uint8_t v___x_945_, lean_object* v_a_946_, lean_object* v_ys_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_ctors_940_, v_a_941_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; 
lean_dec(v_a_941_);
v_val_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_954_, 1);
lean_inc_ref(v_ys_947_);
v___x_956_ = lean_array_pop(v_ys_947_);
v___x_957_ = lean_array_get_borrowed(v___x_942_, v_a_943_, v_val_955_);
lean_dec(v_val_955_);
lean_inc(v___x_957_);
v___x_958_ = l_Lean_mkAppN(v___x_957_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_959_ = 1;
v___x_960_ = l_Lean_Meta_mkLambdaFVars(v_ys_947_, v___x_958_, v___x_944_, v___x_945_, v___x_944_, v___x_945_, v___x_959_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec_ref(v_ys_947_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v___x_954_);
v___x_961_ = lean_array_get_size(v_ys_947_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_sub(v___x_961_, v___x_962_);
v___x_964_ = lean_array_get_borrowed(v___x_942_, v_ys_947_, v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_941_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_cidx_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v_cidx_967_ = lean_ctor_get(v_a_966_, 2);
lean_inc(v_cidx_967_);
lean_dec(v_a_966_);
v___x_968_ = l_Lean_mkRawNatLit(v_cidx_967_);
v___x_969_ = l_Lean_mkHasNotBitProof(v___x_968_, v_a_946_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
lean_inc(v___x_964_);
v___x_971_ = l_Lean_Expr_app___override(v___x_964_, v_a_970_);
v___x_972_ = 1;
v___x_973_ = l_Lean_Meta_mkLambdaFVars(v_ys_947_, v___x_971_, v___x_944_, v___x_945_, v___x_944_, v___x_945_, v___x_972_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec_ref(v_ys_947_);
return v___x_973_;
}
else
{
lean_dec_ref(v_ys_947_);
return v___x_969_;
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_ys_947_);
v_a_974_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_965_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_965_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctors_940_ = stack[0].m_obj;
lean_object* v_a_941_ = stack[1].m_obj;
lean_object* v___x_942_ = stack[2].m_obj;
lean_object* v_a_943_ = stack[3].m_obj;
uint8_t v___x_944_ = stack[4].m_num;
uint8_t v___x_945_ = stack[5].m_num;
lean_object* v_a_946_ = stack[6].m_obj;
lean_object* v_ys_947_ = stack[7].m_obj;
lean_object* v_x_948_ = stack[8].m_obj;
lean_object* v___y_949_ = stack[9].m_obj;
lean_object* v___y_950_ = stack[10].m_obj;
lean_object* v___y_951_ = stack[11].m_obj;
lean_object* v___y_952_ = stack[12].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(v_ctors_940_, v_a_941_, v___x_942_, v_a_943_, v___x_944_, v___x_945_, v_a_946_, v_ys_947_, v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object* v_ctors_983_, lean_object* v_a_984_, lean_object* v___x_985_, lean_object* v_a_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_a_989_, lean_object* v_ys_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v___x_23157__boxed_997_; uint8_t v___x_23158__boxed_998_; lean_object* v_res_999_; 
v___x_23157__boxed_997_ = lean_unbox(v___x_987_);
v___x_23158__boxed_998_ = lean_unbox(v___x_988_);
v_res_999_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(v_ctors_983_, v_a_984_, v___x_985_, v_a_986_, v___x_23157__boxed_997_, v___x_23158__boxed_998_, v_a_989_, v_ys_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_x_991_);
lean_dec_ref(v_a_989_);
lean_dec_ref(v_a_986_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v_ctors_983_);
return v_res_999_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_ctors_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_as_1003_, lean_object* v_bs_1004_, lean_object* v_i_1005_, lean_object* v_cs_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_array_get_size(v_as_1003_);
v___x_1013_ = lean_nat_dec_lt(v_i_1005_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v_i_1005_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_ctors_1000_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_cs_1006_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_array_get_size(v_bs_1004_);
v___x_1016_ = lean_nat_dec_lt(v_i_1005_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec(v_i_1005_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_ctors_1000_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_cs_1006_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v_b_1024_; lean_object* v___x_1025_; 
v___x_1018_ = l_Lean_instInhabitedExpr;
v___x_1019_ = 0;
v_a_1020_ = lean_array_fget_borrowed(v_as_1003_, v_i_1005_);
v___x_1021_ = lean_box(v___x_1019_);
v___x_1022_ = lean_box(v___x_1016_);
lean_inc_ref(v_a_1002_);
lean_inc_ref(v_a_1001_);
lean_inc(v_a_1020_);
lean_inc_ref(v_ctors_1000_);
v___f_1023_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1023_, 0, v_ctors_1000_);
lean_closure_set(v___f_1023_, 1, v_a_1020_);
lean_closure_set(v___f_1023_, 2, v___x_1018_);
lean_closure_set(v___f_1023_, 3, v_a_1001_);
lean_closure_set(v___f_1023_, 4, v___x_1021_);
lean_closure_set(v___f_1023_, 5, v___x_1022_);
lean_closure_set(v___f_1023_, 6, v_a_1002_);
v_b_1024_ = lean_array_fget_borrowed(v_bs_1004_, v_i_1005_);
lean_inc(v_b_1024_);
v___x_1025_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_b_1024_, v___f_1023_, v___x_1019_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_i_1005_, v___x_1027_);
lean_dec(v_i_1005_);
v___x_1029_ = lean_array_push(v_cs_1006_, v_a_1026_);
v_i_1005_ = v___x_1028_;
v_cs_1006_ = v___x_1029_;
goto _start;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_cs_1006_);
lean_dec(v_i_1005_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_ctors_1000_);
v_a_1031_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1025_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1025_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctors_1000_ = stack[0].m_obj;
lean_object* v_a_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v_as_1003_ = stack[3].m_obj;
lean_object* v_bs_1004_ = stack[4].m_obj;
lean_object* v_i_1005_ = stack[5].m_obj;
lean_object* v_cs_1006_ = stack[6].m_obj;
lean_object* v___y_1007_ = stack[7].m_obj;
lean_object* v___y_1008_ = stack[8].m_obj;
lean_object* v___y_1009_ = stack[9].m_obj;
lean_object* v___y_1010_ = stack[10].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1000_, v_a_1001_, v_a_1002_, v_as_1003_, v_bs_1004_, v_i_1005_, v_cs_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_ctors_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_as_1043_, lean_object* v_bs_1044_, lean_object* v_i_1045_, lean_object* v_cs_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1040_, v_a_1041_, v_a_1042_, v_as_1043_, v_bs_1044_, v_i_1045_, v_cs_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_bs_1044_);
lean_dec_ref(v_as_1043_);
return v_res_1052_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object* v_k_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v___x_1060_ = lean_apply_6(v_k_1053_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, lean_box(0));
return v___x_1060_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1053_ = stack[0].m_obj;
lean_object* v_b_1054_ = stack[1].m_obj;
lean_object* v___y_1055_ = stack[2].m_obj;
lean_object* v___y_1056_ = stack[3].m_obj;
lean_object* v___y_1057_ = stack[4].m_obj;
lean_object* v___y_1058_ = stack[5].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(v_k_1053_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v_k_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(v_k_1062_, v_b_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object* v_name_1070_, uint8_t v_bi_1071_, lean_object* v_type_1072_, lean_object* v_k_1073_, uint8_t v_kind_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1080_, 0, v_k_1073_);
v___x_1081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1070_, v_bi_1071_, v_type_1072_, v___f_1080_, v_kind_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1081_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1081_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1070_ = stack[0].m_obj;
uint8_t v_bi_1071_ = stack[1].m_num;
lean_object* v_type_1072_ = stack[2].m_obj;
lean_object* v_k_1073_ = stack[3].m_obj;
uint8_t v_kind_1074_ = stack[4].m_num;
lean_object* v___y_1075_ = stack[5].m_obj;
lean_object* v___y_1076_ = stack[6].m_obj;
lean_object* v___y_1077_ = stack[7].m_obj;
lean_object* v___y_1078_ = stack[8].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1070_, v_bi_1071_, v_type_1072_, v_k_1073_, v_kind_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object* v_name_1099_, lean_object* v_bi_1100_, lean_object* v_type_1101_, lean_object* v_k_1102_, lean_object* v_kind_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v_bi_boxed_1109_; uint8_t v_kind_boxed_1110_; lean_object* v_res_1111_; 
v_bi_boxed_1109_ = lean_unbox(v_bi_1100_);
v_kind_boxed_1110_ = lean_unbox(v_kind_1103_);
v_res_1111_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1099_, v_bi_boxed_1109_, v_type_1101_, v_k_1102_, v_kind_boxed_1110_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1111_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object* v_name_1112_, lean_object* v_type_1113_, lean_object* v_k_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = 0;
v___x_1121_ = 0;
v___x_1122_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1112_, v___x_1120_, v_type_1113_, v_k_1114_, v___x_1121_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v___x_1122_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1112_ = stack[0].m_obj;
lean_object* v_type_1113_ = stack[1].m_obj;
lean_object* v_k_1114_ = stack[2].m_obj;
lean_object* v___y_1115_ = stack[3].m_obj;
lean_object* v___y_1116_ = stack[4].m_obj;
lean_object* v___y_1117_ = stack[5].m_obj;
lean_object* v___y_1118_ = stack[6].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_1112_, v_type_1113_, v_k_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object* v_name_1124_, lean_object* v_type_1125_, lean_object* v_k_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_1124_, v_type_1125_, v_k_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_bs_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_bs_1135_);
return v___x_1142_;
}
else
{
lean_object* v_v_1143_; lean_object* v___x_1144_; lean_object* v_bs_x27_1145_; lean_object* v___x_1146_; 
v_v_1143_ = lean_array_uget(v_bs_1135_, v_i_1134_);
v___x_1144_ = lean_unsigned_to_nat(0u);
v_bs_x27_1145_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1144_);
v___x_1146_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1143_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v_cidx_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v_cidx_1148_ = lean_ctor_get(v_a_1147_, 2);
lean_inc(v_cidx_1148_);
lean_dec(v_a_1147_);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1134_, v___x_1149_);
v___x_1151_ = lean_array_uset(v_bs_x27_1145_, v_i_1134_, v_cidx_1148_);
v_i_1134_ = v___x_1150_;
v_bs_1135_ = v___x_1151_;
goto _start;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_bs_x27_1145_);
v_a_1153_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1146_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1146_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1133_ = stack[0].m_num;
size_t v_i_1134_ = stack[1].m_num;
lean_object* v_bs_1135_ = stack[2].m_obj;
lean_object* v___y_1136_ = stack[3].m_obj;
lean_object* v___y_1137_ = stack[4].m_obj;
lean_object* v___y_1138_ = stack[5].m_obj;
lean_object* v___y_1139_ = stack[6].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_1133_, v_i_1134_, v_bs_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_bs_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_sz_boxed_1170_; size_t v_i_boxed_1171_; lean_object* v_res_1172_; 
v_sz_boxed_1170_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1171_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_boxed_1170_, v_i_boxed_1171_, v_bs_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1172_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object* v___x_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_bs_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_bs_1176_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v_v_1185_; lean_object* v___x_1186_; lean_object* v_bs_x27_1187_; lean_object* v_a_1189_; lean_object* v___x_1194_; 
v___x_1184_ = l_Lean_instInhabitedExpr;
v_v_1185_ = lean_array_uget(v_bs_1176_, v_i_1175_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v_bs_x27_1187_ = lean_array_uset(v_bs_1176_, v_i_1175_, v___x_1186_);
v___x_1194_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1185_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_cidx_1196_; lean_object* v_start_1197_; lean_object* v_stop_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_cidx_1196_ = lean_ctor_get(v_a_1195_, 2);
lean_inc(v_cidx_1196_);
lean_dec(v_a_1195_);
v_start_1197_ = lean_ctor_get(v___x_1173_, 1);
v_stop_1198_ = lean_ctor_get(v___x_1173_, 2);
v___x_1199_ = lean_nat_sub(v_stop_1198_, v_start_1197_);
v___x_1200_ = lean_nat_dec_lt(v_cidx_1196_, v___x_1199_);
lean_dec(v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec(v_cidx_1196_);
v___x_1201_ = l_outOfBounds___redArg(v___x_1184_);
v_a_1189_ = v___x_1201_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Subarray_get___redArg(v___x_1173_, v_cidx_1196_);
lean_dec(v_cidx_1196_);
v_a_1189_ = v___x_1202_;
goto v___jp_1188_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_bs_x27_1187_);
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
v___jp_1188_:
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1175_, v___x_1190_);
v___x_1192_ = lean_array_uset(v_bs_x27_1187_, v_i_1175_, v_a_1189_);
v_i_1175_ = v___x_1191_;
v_bs_1176_ = v___x_1192_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1173_ = stack[0].m_obj;
size_t v_sz_1174_ = stack[1].m_num;
size_t v_i_1175_ = stack[2].m_num;
lean_object* v_bs_1176_ = stack[3].m_obj;
lean_object* v___y_1177_ = stack[4].m_obj;
lean_object* v___y_1178_ = stack[5].m_obj;
lean_object* v___y_1179_ = stack[6].m_obj;
lean_object* v___y_1180_ = stack[7].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1173_, v_sz_1174_, v_i_1175_, v_bs_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v___x_1212_, lean_object* v_sz_1213_, lean_object* v_i_1214_, lean_object* v_bs_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
size_t v_sz_boxed_1221_; size_t v_i_boxed_1222_; lean_object* v_res_1223_; 
v_sz_boxed_1221_ = lean_unbox_usize(v_sz_1213_);
lean_dec(v_sz_1213_);
v_i_boxed_1222_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1212_, v_sz_boxed_1221_, v_i_boxed_1222_, v_bs_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___x_1212_);
return v_res_1223_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1235_, lean_object* v___x_1236_, lean_object* v_numIndices_1237_, uint8_t v___x_1238_, lean_object* v_ctors_1239_, lean_object* v___x_1240_, lean_object* v___x_1241_, lean_object* v_a_1242_, lean_object* v_ctors_1243_, lean_object* v___x_1244_, lean_object* v_xs_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1360_ = lean_array_get_size(v_xs_1245_);
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_nat_add(v_numParams_1235_, v___x_1361_);
v___x_1363_ = lean_nat_add(v___x_1362_, v_numIndices_1237_);
lean_dec(v___x_1362_);
v___x_1364_ = lean_nat_add(v___x_1363_, v___x_1361_);
lean_dec(v___x_1363_);
v___x_1365_ = l_List_lengthTR___redArg(v_ctors_1243_);
v___x_1366_ = lean_nat_add(v___x_1364_, v___x_1365_);
lean_dec(v___x_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_nat_dec_eq(v___x_1360_, v___x_1366_);
lean_dec(v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_xs_1245_);
lean_dec(v_ctors_1243_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
lean_dec_ref(v_ctors_1239_);
lean_dec(v_numParams_1235_);
v___x_1368_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1369_ = l_Lean_MessageData_ofConstName(v___x_1244_, v___x_1367_);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1372_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_dec(v___x_1244_);
v___y_1253_ = v___y_1247_;
v___y_1254_ = v___y_1248_;
v___y_1255_ = v___y_1249_;
v___y_1256_ = v___y_1250_;
goto v___jp_1252_;
}
v___jp_1252_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1257_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1235_);
lean_inc_ref_n(v_xs_1245_, 2);
v___x_1258_ = l_Array_toSubarray___redArg(v_xs_1245_, v___x_1257_, v_numParams_1235_);
v___x_1259_ = lean_array_get(v___x_1236_, v_xs_1245_, v_numParams_1235_);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_numParams_1235_, v___x_1260_);
lean_dec(v_numParams_1235_);
v___x_1262_ = lean_nat_add(v___x_1261_, v_numIndices_1237_);
lean_inc(v___x_1262_);
v___x_1263_ = l_Array_toSubarray___redArg(v_xs_1245_, v___x_1261_, v___x_1262_);
v___x_1264_ = lean_array_get(v___x_1236_, v_xs_1245_, v___x_1262_);
v___x_1265_ = l_Subarray_copy___redArg(v___x_1263_);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1260_);
lean_inc(v___x_1264_);
lean_inc_ref_n(v___x_1266_, 2);
v___x_1267_ = lean_array_push(v___x_1266_, v___x_1264_);
lean_inc_ref(v___x_1265_);
v___x_1268_ = l_Array_append___redArg(v___x_1265_, v___x_1267_);
v___x_1269_ = lean_box(v___x_1238_);
lean_inc_ref(v___x_1268_);
lean_inc(v___x_1259_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1270_, 0, v___x_1266_);
lean_closure_set(v___f_1270_, 1, v___x_1259_);
lean_closure_set(v___f_1270_, 2, v___x_1268_);
lean_closure_set(v___f_1270_, 3, v___x_1269_);
v___x_1271_ = lean_nat_add(v___x_1262_, v___x_1260_);
lean_dec(v___x_1262_);
v___x_1272_ = lean_array_get_size(v_xs_1245_);
v___x_1273_ = l_Array_toSubarray___redArg(v_xs_1245_, v___x_1271_, v___x_1272_);
v_sz_1274_ = lean_array_size(v_ctors_1239_);
v___x_1275_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1239_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1273_, v_sz_1274_, v___x_1275_, v_ctors_1239_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v___x_1273_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
lean_inc_ref(v_ctors_1239_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_1274_, v___x_1275_, v_ctors_1239_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = l_Lean_mkConst(v___x_1240_, v___x_1241_);
v___x_1281_ = l_Subarray_copy___redArg(v___x_1258_);
lean_inc_ref(v___x_1281_);
v___x_1282_ = l_Array_append___redArg(v___x_1281_, v___x_1265_);
v___x_1283_ = l_Array_append___redArg(v___x_1282_, v___x_1267_);
v___x_1284_ = l_Lean_mkAppN(v___x_1280_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_mkHasNotBit(v___x_1284_, v_a_1279_);
v___x_1286_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1287_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v___x_1286_, v___x_1285_, v___f_1270_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = l_Lean_ConstantInfo_value_x21(v_a_1242_, v___x_1238_);
v___x_1290_ = l_Lean_mkAppN(v___x_1289_, v___x_1281_);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1292_ = l_Lean_Core_mkFreshUserName(v___x_1291_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = 0;
lean_inc(v___x_1259_);
v___x_1295_ = l_Lean_mkAppN(v___x_1259_, v___x_1268_);
v___x_1296_ = l_Lean_mkForall(v_a_1293_, v___x_1294_, v_a_1288_, v___x_1295_);
v___x_1297_ = 1;
v___x_1298_ = 1;
v___x_1299_ = l_Lean_Meta_mkLambdaFVars(v___x_1268_, v___x_1296_, v___x_1238_, v___x_1297_, v___x_1238_, v___x_1297_, v___x_1298_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v___x_1268_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = l_Lean_Expr_app___override(v___x_1290_, v_a_1300_);
v___x_1302_ = l_Lean_mkAppN(v___x_1301_, v___x_1265_);
v___x_1303_ = l_Lean_Expr_app___override(v___x_1302_, v___x_1264_);
v___x_1304_ = l_List_lengthTR___redArg(v_ctors_1243_);
lean_inc_ref(v___x_1303_);
v___x_1305_ = l_Lean_Meta_inferArgumentTypesN(v___x_1304_, v___x_1303_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = lean_array_mk(v_ctors_1243_);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1277_);
v___x_1309_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1239_, v_a_1277_, v_a_1279_, v___x_1307_, v_a_1306_, v___x_1257_, v___x_1308_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v_a_1306_);
lean_dec_ref(v___x_1307_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l_Lean_mkAppN(v___x_1303_, v_a_1310_);
lean_dec(v_a_1310_);
v___x_1312_ = l_Lean_Core_betaReduce(v___x_1311_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = lean_array_push(v___x_1266_, v___x_1259_);
v___x_1315_ = l_Array_append___redArg(v___x_1281_, v___x_1314_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = l_Array_append___redArg(v___x_1315_, v___x_1265_);
lean_dec_ref(v___x_1265_);
v___x_1317_ = l_Array_append___redArg(v___x_1316_, v___x_1267_);
lean_dec_ref(v___x_1267_);
v___x_1318_ = l_Array_append___redArg(v___x_1317_, v_a_1277_);
lean_dec(v_a_1277_);
v___x_1319_ = l_Lean_Meta_mkLambdaFVars(v___x_1318_, v_a_1313_, v___x_1238_, v___x_1297_, v___x_1238_, v___x_1297_, v___x_1298_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v___x_1318_);
return v___x_1319_;
}
else
{
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1259_);
return v___x_1312_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1259_);
v_a_1320_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1309_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1309_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1279_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1259_);
lean_dec(v_ctors_1243_);
lean_dec_ref(v_ctors_1239_);
v_a_1328_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1305_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1305_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1279_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1264_);
lean_dec(v___x_1259_);
lean_dec(v_ctors_1243_);
lean_dec_ref(v_ctors_1239_);
return v___x_1299_;
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v___x_1290_);
lean_dec(v_a_1288_);
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1279_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1264_);
lean_dec(v___x_1259_);
lean_dec(v_ctors_1243_);
lean_dec_ref(v_ctors_1239_);
v_a_1336_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1292_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1292_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_dec_ref(v___x_1281_);
lean_dec(v_a_1279_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1264_);
lean_dec(v___x_1259_);
lean_dec(v_ctors_1243_);
lean_dec_ref(v_ctors_1239_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_a_1277_);
lean_dec_ref(v___f_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1264_);
lean_dec(v___x_1259_);
lean_dec_ref(v___x_1258_);
lean_dec(v_ctors_1243_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
lean_dec_ref(v_ctors_1239_);
v_a_1344_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1278_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1278_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v___f_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v___x_1264_);
lean_dec(v___x_1259_);
lean_dec_ref(v___x_1258_);
lean_dec(v_ctors_1243_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
lean_dec_ref(v_ctors_1239_);
v_a_1352_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1276_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1276_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkSparseCasesOn___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_1235_ = stack[0].m_obj;
lean_object* v___x_1236_ = stack[1].m_obj;
lean_object* v_numIndices_1237_ = stack[2].m_obj;
uint8_t v___x_1238_ = stack[3].m_num;
lean_object* v_ctors_1239_ = stack[4].m_obj;
lean_object* v___x_1240_ = stack[5].m_obj;
lean_object* v___x_1241_ = stack[6].m_obj;
lean_object* v_a_1242_ = stack[7].m_obj;
lean_object* v_ctors_1243_ = stack[8].m_obj;
lean_object* v___x_1244_ = stack[9].m_obj;
lean_object* v_xs_1245_ = stack[10].m_obj;
lean_object* v_x_1246_ = stack[11].m_obj;
lean_object* v___y_1247_ = stack[12].m_obj;
lean_object* v___y_1248_ = stack[13].m_obj;
lean_object* v___y_1249_ = stack[14].m_obj;
lean_object* v___y_1250_ = stack[15].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1235_, v___x_1236_, v_numIndices_1237_, v___x_1238_, v_ctors_1239_, v___x_1240_, v___x_1241_, v_a_1242_, v_ctors_1243_, v___x_1244_, v_xs_1245_, v_x_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1383_ = _args[0];
lean_object* v___x_1384_ = _args[1];
lean_object* v_numIndices_1385_ = _args[2];
lean_object* v___x_1386_ = _args[3];
lean_object* v_ctors_1387_ = _args[4];
lean_object* v___x_1388_ = _args[5];
lean_object* v___x_1389_ = _args[6];
lean_object* v_a_1390_ = _args[7];
lean_object* v_ctors_1391_ = _args[8];
lean_object* v___x_1392_ = _args[9];
lean_object* v_xs_1393_ = _args[10];
lean_object* v_x_1394_ = _args[11];
lean_object* v___y_1395_ = _args[12];
lean_object* v___y_1396_ = _args[13];
lean_object* v___y_1397_ = _args[14];
lean_object* v___y_1398_ = _args[15];
lean_object* v___y_1399_ = _args[16];
_start:
{
uint8_t v___x_23747__boxed_1400_; lean_object* v_res_1401_; 
v___x_23747__boxed_1400_ = lean_unbox(v___x_1386_);
v_res_1401_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1383_, v___x_1384_, v_numIndices_1385_, v___x_23747__boxed_1400_, v_ctors_1387_, v___x_1388_, v___x_1389_, v_a_1390_, v_ctors_1391_, v___x_1392_, v_xs_1393_, v_x_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec_ref(v_x_1394_);
lean_dec_ref(v_a_1390_);
lean_dec(v_numIndices_1385_);
lean_dec_ref(v___x_1384_);
return v_res_1401_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object* v_ref_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_toCold_1409_; lean_object* v_currRecDepth_1410_; lean_object* v_ref_1411_; uint16_t v_optionFlags_1412_; uint8_t v_suppressElabErrors_1413_; uint8_t v_isRecordingDeps_1414_; lean_object* v_ref_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_toCold_1409_ = lean_ctor_get(v___y_1406_, 0);
v_currRecDepth_1410_ = lean_ctor_get(v___y_1406_, 1);
v_ref_1411_ = lean_ctor_get(v___y_1406_, 2);
v_optionFlags_1412_ = lean_ctor_get_uint16(v___y_1406_, sizeof(void*)*3);
v_suppressElabErrors_1413_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1414_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 3);
v_ref_1415_ = l_Lean_replaceRef(v_ref_1402_, v_ref_1411_);
lean_inc(v_currRecDepth_1410_);
lean_inc_ref(v_toCold_1409_);
v___x_1416_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1416_, 0, v_toCold_1409_);
lean_ctor_set(v___x_1416_, 1, v_currRecDepth_1410_);
lean_ctor_set(v___x_1416_, 2, v_ref_1415_);
lean_ctor_set_uint16(v___x_1416_, sizeof(void*)*3, v_optionFlags_1412_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3 + 2, v_suppressElabErrors_1413_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3 + 3, v_isRecordingDeps_1414_);
v___x_1417_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_1403_, v___y_1404_, v___y_1405_, v___x_1416_, v___y_1407_);
lean_dec_ref_known(v___x_1416_, 3);
return v___x_1417_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1402_ = stack[0].m_obj;
lean_object* v_msg_1403_ = stack[1].m_obj;
lean_object* v___y_1404_ = stack[2].m_obj;
lean_object* v___y_1405_ = stack[3].m_obj;
lean_object* v___y_1406_ = stack[4].m_obj;
lean_object* v___y_1407_ = stack[5].m_obj;
lean_object* v_res_1418_;
v_res_1418_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
stack->m_obj
 = v_res_1418_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object* v_ref_1419_, lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1419_, v_msg_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v_ref_1419_);
return v_res_1426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1430_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_ctor_set(v___x_1432_, 2, v___x_1431_);
lean_ctor_set(v___x_1432_, 3, v___x_1431_);
lean_ctor_set(v___x_1432_, 4, v___x_1430_);
lean_ctor_set(v___x_1432_, 5, v___x_1430_);
lean_ctor_set(v___x_1432_, 6, v___x_1430_);
lean_ctor_set(v___x_1432_, 7, v___x_1430_);
lean_ctor_set(v___x_1432_, 8, v___x_1430_);
lean_ctor_set(v___x_1432_, 9, v___x_1430_);
lean_ctor_set(v___x_1432_, 10, v___x_1430_);
lean_ctor_set(v___x_1432_, 11, v___x_1429_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(32u);
v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3(void){
_start:
{
size_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1436_ = ((size_t)5ULL);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_unsigned_to_nat(32u);
v___x_1439_ = lean_mk_empty_array_with_capacity(v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2);
v___x_1441_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
lean_ctor_set(v___x_1441_, 2, v___x_1437_);
lean_ctor_set(v___x_1441_, 3, v___x_1437_);
lean_ctor_set_usize(v___x_1441_, 4, v___x_1436_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1442_ = lean_box(1);
v___x_1443_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3);
v___x_1444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v___x_1442_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17));
v___x_1466_ = l_Lean_stringToMessageData(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__19));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__21));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__23));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__25));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object* v_msg_1479_, lean_object* v_declHint_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_env_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_st_ref_get(v___y_1481_);
v_env_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_ref(v_env_1485_);
lean_dec(v___x_1484_);
v___x_1486_ = l_Lean_Name_isAnonymous(v_declHint_1480_);
if (v___x_1486_ == 0)
{
uint8_t v_isExporting_1487_; 
v_isExporting_1487_ = lean_ctor_get_uint8(v_env_1485_, sizeof(void*)*13);
if (v_isExporting_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec_ref(v_env_1485_);
lean_dec(v_declHint_1480_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_msg_1479_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
lean_inc_ref(v_env_1485_);
v___x_1489_ = l_Lean_Environment_setExporting(v_env_1485_, v___x_1486_);
lean_inc(v_declHint_1480_);
lean_inc_ref(v___x_1489_);
v___x_1490_ = l_Lean_Environment_contains(v___x_1489_, v_declHint_1480_, v_isExporting_1487_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_env_1485_);
lean_dec(v_declHint_1480_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_msg_1479_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_c_1497_; lean_object* v___x_1498_; 
v___x_1492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1);
v___x_1493_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4);
v___x_1494_ = l_Lean_Options_empty;
v___x_1495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1489_);
lean_ctor_set(v___x_1495_, 1, v___x_1492_);
lean_ctor_set(v___x_1495_, 2, v___x_1493_);
lean_ctor_set(v___x_1495_, 3, v___x_1494_);
lean_inc(v_declHint_1480_);
v___x_1496_ = l_Lean_MessageData_ofConstName(v_declHint_1480_, v___x_1486_);
v_c_1497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1497_, 0, v___x_1495_);
lean_ctor_set(v_c_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1485_, v_declHint_1480_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_env_1485_);
lean_dec(v_declHint_1480_);
v___x_1499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_c_1497_);
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_MessageData_note(v___x_1502_);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_msg_1479_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1562_; 
v_val_1506_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1508_ = v___x_1498_;
v_isShared_1509_ = v_isSharedCheck_1562_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1498_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1562_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v_modules_1511_; lean_object* v_moduleNames_1512_; lean_object* v_mod_1513_; uint8_t v___y_1515_; uint8_t v___x_1545_; 
v___x_1510_ = l_Lean_Environment_header(v_env_1485_);
lean_dec_ref(v_env_1485_);
v_modules_1511_ = lean_ctor_get(v___x_1510_, 3);
lean_inc_ref(v_modules_1511_);
v_moduleNames_1512_ = lean_ctor_get(v___x_1510_, 4);
lean_inc_ref(v_moduleNames_1512_);
lean_dec_ref(v___x_1510_);
v_mod_1513_ = lean_array_get(v___x_1483_, v_moduleNames_1512_, v_val_1506_);
lean_dec_ref(v_moduleNames_1512_);
v___x_1545_ = l_Lean_isPrivateName(v_declHint_1480_);
lean_dec(v_declHint_1480_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_array_get_size(v_modules_1511_);
v___x_1547_ = lean_nat_dec_lt(v_val_1506_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_dec_ref(v_modules_1511_);
lean_dec(v_val_1506_);
v___y_1515_ = v___x_1545_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1548_; lean_object* v_toImport_1549_; uint8_t v_isExported_1550_; 
v___x_1548_ = lean_array_fget(v_modules_1511_, v_val_1506_);
lean_dec(v_val_1506_);
lean_dec_ref(v_modules_1511_);
v_toImport_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_ref(v_toImport_1549_);
lean_dec(v___x_1548_);
v_isExported_1550_ = lean_ctor_get_uint8(v_toImport_1549_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1549_);
v___y_1515_ = v_isExported_1550_;
goto v___jp_1514_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v_modules_1511_);
lean_del_object(v___x_1508_);
lean_dec(v_val_1506_);
v___x_1551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v_c_1497_);
v___x_1553_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__24);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_MessageData_ofName(v_mod_1513_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__26);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_note(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_msg_1479_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
v___jp_1514_:
{
if (v___y_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v_c_1497_);
v___x_1518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_MessageData_ofName(v_mod_1513_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_MessageData_note(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_msg_1479_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1525_);
v___x_1527_ = v___x_1508_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1529_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_c_1497_);
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_MessageData_ofName(v_mod_1513_);
lean_inc_ref(v___x_1533_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__20);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1533_);
v___x_1538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__22);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_MessageData_note(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_msg_1479_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1541_);
v___x_1543_ = v___x_1508_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
}
else
{
lean_object* v___x_1563_; 
lean_dec_ref(v_env_1485_);
lean_dec(v_declHint_1480_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_msg_1479_);
return v___x_1563_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1479_ = stack[0].m_obj;
lean_object* v_declHint_1480_ = stack[1].m_obj;
lean_object* v___y_1481_ = stack[2].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1479_, v_declHint_1480_, v___y_1481_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object* v_msg_1565_, lean_object* v_declHint_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1565_, v_declHint_1566_, v___y_1567_);
lean_dec(v___y_1567_);
return v_res_1569_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object* v_msg_1570_, lean_object* v_declHint_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1587_; 
v___x_1577_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1570_, v_declHint_1571_, v___y_1575_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = l_Lean_unknownIdentifierMessageTag;
v___x_1583_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1570_ = stack[0].m_obj;
lean_object* v_declHint_1571_ = stack[1].m_obj;
lean_object* v___y_1572_ = stack[2].m_obj;
lean_object* v___y_1573_ = stack[3].m_obj;
lean_object* v___y_1574_ = stack[4].m_obj;
lean_object* v___y_1575_ = stack[5].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1570_, v_declHint_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object* v_msg_1589_, lean_object* v_declHint_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1589_, v_declHint_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1596_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object* v_ref_1597_, lean_object* v_msg_1598_, lean_object* v_declHint_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v_a_1606_; lean_object* v___x_1607_; 
v___x_1605_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1598_, v_declHint_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1597_, v_a_1606_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
return v___x_1607_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1597_ = stack[0].m_obj;
lean_object* v_msg_1598_ = stack[1].m_obj;
lean_object* v_declHint_1599_ = stack[2].m_obj;
lean_object* v___y_1600_ = stack[3].m_obj;
lean_object* v___y_1601_ = stack[4].m_obj;
lean_object* v___y_1602_ = stack[5].m_obj;
lean_object* v___y_1603_ = stack[6].m_obj;
lean_object* v_res_1608_;
v_res_1608_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1597_, v_msg_1598_, v_declHint_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
stack->m_obj
 = v_res_1608_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object* v_ref_1609_, lean_object* v_msg_1610_, lean_object* v_declHint_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1609_, v_msg_1610_, v_declHint_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_ref_1609_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object* v_ref_1621_, lean_object* v_constName_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1628_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1);
v___x_1629_ = 0;
lean_inc(v_constName_1622_);
v___x_1630_ = l_Lean_MessageData_ofConstName(v_constName_1622_, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1621_, v___x_1633_, v_constName_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1634_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1621_ = stack[0].m_obj;
lean_object* v_constName_1622_ = stack[1].m_obj;
lean_object* v___y_1623_ = stack[2].m_obj;
lean_object* v___y_1624_ = stack[3].m_obj;
lean_object* v___y_1625_ = stack[4].m_obj;
lean_object* v___y_1626_ = stack[5].m_obj;
lean_object* v_res_1635_;
v_res_1635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1621_, v_constName_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
stack->m_obj
 = v_res_1635_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object* v_ref_1636_, lean_object* v_constName_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1636_, v_constName_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v_ref_1636_);
return v_res_1643_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object* v_constName_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_ref_1650_; lean_object* v___x_1651_; 
v_ref_1650_ = lean_ctor_get(v___y_1647_, 2);
v___x_1651_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1650_, v_constName_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1644_ = stack[0].m_obj;
lean_object* v___y_1645_ = stack[1].m_obj;
lean_object* v___y_1646_ = stack[2].m_obj;
lean_object* v___y_1647_ = stack[3].m_obj;
lean_object* v___y_1648_ = stack[4].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object* v_constName_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1659_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_constName_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_env_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1666_ = lean_st_ref_get(v___y_1664_);
v_env_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_ref(v_env_1667_);
lean_dec(v___x_1666_);
v___x_1668_ = 0;
lean_inc(v_constName_1660_);
v___x_1669_ = l_Lean_Environment_find_x3f(v_env_1667_, v_constName_1660_, v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1670_;
}
else
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_constName_1660_);
v_val_1671_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1669_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v___x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_val_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1660_ = stack[0].m_obj;
lean_object* v___y_1661_ = stack[1].m_obj;
lean_object* v___y_1662_ = stack[2].m_obj;
lean_object* v___y_1663_ = stack[3].m_obj;
lean_object* v___y_1664_ = stack[4].m_obj;
lean_object* v_res_1679_;
v_res_1679_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_constName_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
stack->m_obj
 = v_res_1679_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object* v_constName_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_constName_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1686_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1692_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
lean_ctor_set(v___x_1692_, 2, v___x_1691_);
lean_ctor_set(v___x_1692_, 3, v___x_1691_);
lean_ctor_set(v___x_1692_, 4, v___x_1691_);
lean_ctor_set(v___x_1692_, 5, v___x_1691_);
return v___x_1692_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object* v_declName_1693_, uint8_t v_s_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_env_1699_; lean_object* v_nextMacroScope_1700_; lean_object* v_ngen_1701_; lean_object* v_auxDeclNGen_1702_; lean_object* v_traceState_1703_; lean_object* v_recordedDeps_1704_; lean_object* v_messages_1705_; lean_object* v_infoState_1706_; lean_object* v_snapshotTasks_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1736_; 
v___x_1698_ = lean_st_ref_take(v___y_1696_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1700_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1701_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1702_ = lean_ctor_get(v___x_1698_, 3);
v_traceState_1703_ = lean_ctor_get(v___x_1698_, 4);
v_recordedDeps_1704_ = lean_ctor_get(v___x_1698_, 6);
v_messages_1705_ = lean_ctor_get(v___x_1698_, 7);
v_infoState_1706_ = lean_ctor_get(v___x_1698_, 8);
v_snapshotTasks_1707_ = lean_ctor_get(v___x_1698_, 9);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1698_, 5);
lean_dec(v_unused_1737_);
v___x_1709_ = v___x_1698_;
v_isShared_1710_ = v_isSharedCheck_1736_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snapshotTasks_1707_);
lean_inc(v_infoState_1706_);
lean_inc(v_messages_1705_);
lean_inc(v_recordedDeps_1704_);
lean_inc(v_traceState_1703_);
lean_inc(v_auxDeclNGen_1702_);
lean_inc(v_ngen_1701_);
lean_inc(v_nextMacroScope_1700_);
lean_inc(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1736_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1711_ = 0;
v___x_1712_ = lean_box(0);
v___x_1713_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1699_, v_declName_1693_, v_s_1694_, v___x_1711_, v___x_1712_);
v___x_1714_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 5, v___x_1714_);
lean_ctor_set(v___x_1709_, 0, v___x_1713_);
v___x_1716_ = v___x_1709_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_nextMacroScope_1700_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_ngen_1701_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_auxDeclNGen_1702_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_traceState_1703_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1735_, 6, v_recordedDeps_1704_);
lean_ctor_set(v_reuseFailAlloc_1735_, 7, v_messages_1705_);
lean_ctor_set(v_reuseFailAlloc_1735_, 8, v_infoState_1706_);
lean_ctor_set(v_reuseFailAlloc_1735_, 9, v_snapshotTasks_1707_);
v___x_1716_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_mctx_1719_; lean_object* v_zetaDeltaFVarIds_1720_; lean_object* v_postponed_1721_; lean_object* v_diag_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
v___x_1717_ = lean_st_ref_put(v___y_1696_, v___x_1716_);
v___x_1718_ = lean_st_ref_take(v___y_1695_);
v_mctx_1719_ = lean_ctor_get(v___x_1718_, 0);
v_zetaDeltaFVarIds_1720_ = lean_ctor_get(v___x_1718_, 2);
v_postponed_1721_ = lean_ctor_get(v___x_1718_, 3);
v_diag_1722_ = lean_ctor_get(v___x_1718_, 4);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1718_, 1);
lean_dec(v_unused_1734_);
v___x_1724_ = v___x_1718_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_diag_1722_);
lean_inc(v_postponed_1721_);
lean_inc(v_zetaDeltaFVarIds_1720_);
lean_inc(v_mctx_1719_);
lean_dec(v___x_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_mctx_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_zetaDeltaFVarIds_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_postponed_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_diag_1722_);
v___x_1729_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_st_ref_put(v___y_1695_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1726_);
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1693_ = stack[0].m_obj;
uint8_t v_s_1694_ = stack[1].m_num;
lean_object* v___y_1695_ = stack[2].m_obj;
lean_object* v___y_1696_ = stack[3].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1693_, v_s_1694_, v___y_1695_, v___y_1696_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object* v_declName_1739_, lean_object* v_s_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v_s_boxed_1744_; lean_object* v_res_1745_; 
v_s_boxed_1744_ = lean_unbox(v_s_1740_);
v_res_1745_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1739_, v_s_boxed_1744_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec(v___y_1741_);
return v_res_1745_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object* v_declName_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = 0;
v___x_1753_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1746_, v___x_1752_, v___y_1748_, v___y_1750_);
return v___x_1753_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1746_ = stack[0].m_obj;
lean_object* v___y_1747_ = stack[1].m_obj;
lean_object* v___y_1748_ = stack[2].m_obj;
lean_object* v___y_1749_ = stack[3].m_obj;
lean_object* v___y_1750_ = stack[4].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_declName_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object* v_declName_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_declName_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = 0;
return v___x_1764_;
}
else
{
lean_object* v_head_1765_; lean_object* v_tail_1766_; uint8_t v___x_1767_; 
v_head_1765_ = lean_ctor_get(v_x_1763_, 0);
v_tail_1766_ = lean_ctor_get(v_x_1763_, 1);
v___x_1767_ = lean_name_eq(v_a_1762_, v_head_1765_);
if (v___x_1767_ == 0)
{
v_x_1763_ = v_tail_1766_;
goto _start;
}
else
{
return v___x_1767_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1762_ = stack[0].m_obj;
lean_object* v_x_1763_ = stack[1].m_obj;
uint8_t v_res_1769_;
v_res_1769_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1762_, v_x_1763_);
stack->m_num = v_res_1769_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1770_, lean_object* v_x_1771_){
_start:
{
uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_res_1772_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1770_, v_x_1771_);
lean_dec(v_x_1771_);
lean_dec(v_a_1770_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object* v_a_1780_, lean_object* v_indName_1781_, lean_object* v_as_1782_, size_t v_sz_1783_, size_t v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_a_1792_; uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_lt(v_i_1784_, v_sz_1783_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec(v_indName_1781_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_b_1785_);
return v___x_1797_;
}
else
{
lean_object* v_ctors_1798_; lean_object* v___x_1799_; lean_object* v_a_1800_; uint8_t v___x_1801_; 
v_ctors_1798_ = lean_ctor_get(v_a_1780_, 4);
v___x_1799_ = lean_box(0);
v_a_1800_ = lean_array_uget_borrowed(v_as_1782_, v_i_1784_);
v___x_1801_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1800_, v_ctors_1798_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1);
lean_inc(v_a_1800_);
v___x_1803_ = l_Lean_MessageData_ofName(v_a_1800_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
lean_inc(v_indName_1781_);
v___x_1807_ = l_Lean_MessageData_ofName(v_indName_1781_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1808_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_dec_ref_known(v___x_1809_, 1);
v_a_1792_ = v___x_1799_;
goto v___jp_1791_;
}
else
{
lean_dec(v_indName_1781_);
return v___x_1809_;
}
}
else
{
v_a_1792_ = v___x_1799_;
goto v___jp_1791_;
}
}
v___jp_1791_:
{
size_t v___x_1793_; size_t v___x_1794_; 
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1784_, v___x_1793_);
v_i_1784_ = v___x_1794_;
v_b_1785_ = v_a_1792_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1780_ = stack[0].m_obj;
lean_object* v_indName_1781_ = stack[1].m_obj;
lean_object* v_as_1782_ = stack[2].m_obj;
size_t v_sz_1783_ = stack[3].m_num;
size_t v_i_1784_ = stack[4].m_num;
lean_object* v_b_1785_ = stack[5].m_obj;
lean_object* v___y_1786_ = stack[6].m_obj;
lean_object* v___y_1787_ = stack[7].m_obj;
lean_object* v___y_1788_ = stack[8].m_obj;
lean_object* v___y_1789_ = stack[9].m_obj;
lean_object* v_res_1810_;
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_1780_, v_indName_1781_, v_as_1782_, v_sz_1783_, v_i_1784_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
stack->m_obj
 = v_res_1810_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object* v_a_1811_, lean_object* v_indName_1812_, lean_object* v_as_1813_, lean_object* v_sz_1814_, lean_object* v_i_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1814_);
lean_dec(v_sz_1814_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_1811_, v_indName_1812_, v_as_1813_, v_sz_boxed_1822_, v_i_boxed_1823_, v_b_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v_as_1813_);
lean_dec_ref(v_a_1811_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
if (lean_obj_tag(v_a_1825_) == 0)
{
lean_object* v___x_1827_; 
v___x_1827_ = l_List_reverse___redArg(v_a_1826_);
return v___x_1827_;
}
else
{
lean_object* v_head_1828_; lean_object* v_tail_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1838_; 
v_head_1828_ = lean_ctor_get(v_a_1825_, 0);
v_tail_1829_ = lean_ctor_get(v_a_1825_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1831_ = v_a_1825_;
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_tail_1829_);
lean_inc(v_head_1828_);
lean_dec(v_a_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = l_Lean_mkLevelParam(v_head_1828_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v_a_1826_);
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1826_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v_a_1825_ = v_tail_1829_;
v_a_1826_ = v___x_1835_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_st_ref_get(v___y_1846_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_env_1849_);
lean_dec(v___x_1848_);
lean_inc(v_constName_1842_);
v___x_1850_ = l_Lean_isInductiveCore_x3f(v_env_1849_, v_constName_1842_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1851_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1852_ = 0;
v___x_1853_ = l_Lean_MessageData_ofConstName(v_constName_1842_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1856_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1857_;
}
else
{
lean_object* v_val_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_constName_1842_);
v_val_1858_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1850_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_val_1858_);
lean_dec(v___x_1850_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 0);
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_val_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1842_ = stack[0].m_obj;
lean_object* v___y_1843_ = stack[1].m_obj;
lean_object* v___y_1844_ = stack[2].m_obj;
lean_object* v___y_1845_ = stack[3].m_obj;
lean_object* v___y_1846_ = stack[4].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1873_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__0(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_1875_ = lean_unsigned_to_nat(42u);
v___x_1876_ = lean_unsigned_to_nat(82u);
v___x_1877_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_1878_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_1879_ = l_mkPanicMessageWithDecl(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1882_ = l_Lean_stringToMessageData(v___x_1881_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__3(void){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__7(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__6));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1890_, lean_object* v_ctors_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_env_2152_; uint8_t v___y_2154_; lean_object* v___x_2210_; uint8_t v_isModule_2211_; 
v___x_1897_ = l_Lean_instInhabitedExpr;
v___x_2150_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__3, &l_Lean_Meta_mkSparseCasesOn___closed__3_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__3);
v___x_2151_ = lean_st_ref_get(v_a_1895_);
v_env_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_ref(v_env_2152_);
lean_dec(v___x_2151_);
v___x_2210_ = l_Lean_Environment_header(v_env_2152_);
v_isModule_2211_ = lean_ctor_get_uint8(v___x_2210_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2210_);
if (v_isModule_2211_ == 0)
{
v___y_2154_ = v_isModule_2211_;
goto v___jp_2153_;
}
else
{
uint8_t v_isExporting_2212_; 
v_isExporting_2212_ = lean_ctor_get_uint8(v_env_2152_, sizeof(void*)*13);
if (v_isExporting_2212_ == 0)
{
v___y_2154_ = v_isModule_2211_;
goto v___jp_2153_;
}
else
{
uint8_t v___x_2213_; 
v___x_2213_ = 0;
v___y_2154_ = v___x_2213_;
goto v___jp_2153_;
}
}
v___jp_1898_:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_ConstantInfo_levelParams(v___y_1907_);
if (lean_obj_tag(v___x_1918_) == 1)
{
lean_object* v_tail_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_tail_1919_ = lean_ctor_get(v___x_1918_, 1);
v___x_1920_ = lean_box(0);
lean_inc(v_tail_1919_);
v___x_1921_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(v_tail_1919_, v___x_1920_);
v___x_1922_ = lean_box(v___y_1905_);
lean_inc_ref(v_ctors_1891_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 17, 10);
lean_closure_set(v___f_1923_, 0, v___y_1899_);
lean_closure_set(v___f_1923_, 1, v___x_1897_);
lean_closure_set(v___f_1923_, 2, v___y_1903_);
lean_closure_set(v___f_1923_, 3, v___x_1922_);
lean_closure_set(v___f_1923_, 4, v_ctors_1891_);
lean_closure_set(v___f_1923_, 5, v___y_1901_);
lean_closure_set(v___f_1923_, 6, v___x_1921_);
lean_closure_set(v___f_1923_, 7, v___y_1902_);
lean_closure_set(v___f_1923_, 8, v___y_1904_);
lean_closure_set(v___f_1923_, 9, v___y_1900_);
v___x_1924_ = l_Lean_ConstantInfo_type(v___y_1907_);
lean_dec_ref(v___y_1907_);
v___x_1925_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v___x_1924_, v___f_1923_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc_n(v_a_1926_, 2);
lean_dec_ref_known(v___x_1925_, 1);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
v___x_1927_ = lean_infer_type(v_a_1926_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_2081_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_box(1);
lean_inc(v___y_1912_);
v___x_1930_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v___y_1912_, v___x_1918_, v_a_1928_, v_a_1926_, v___x_1929_, v___y_1917_);
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_2081_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_2081_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_2080_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_addDecl(v___x_1936_, v___y_1913_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; lean_object* v_env_1939_; lean_object* v_nextMacroScope_1940_; lean_object* v_ngen_1941_; lean_object* v_auxDeclNGen_1942_; lean_object* v_traceState_1943_; lean_object* v_recordedDeps_1944_; lean_object* v_messages_1945_; lean_object* v_infoState_1946_; lean_object* v_snapshotTasks_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref_known(v___x_1937_, 1);
v___x_1938_ = lean_st_ref_take(v___y_1917_);
v_env_1939_ = lean_ctor_get(v___x_1938_, 0);
v_nextMacroScope_1940_ = lean_ctor_get(v___x_1938_, 1);
v_ngen_1941_ = lean_ctor_get(v___x_1938_, 2);
v_auxDeclNGen_1942_ = lean_ctor_get(v___x_1938_, 3);
v_traceState_1943_ = lean_ctor_get(v___x_1938_, 4);
v_recordedDeps_1944_ = lean_ctor_get(v___x_1938_, 6);
v_messages_1945_ = lean_ctor_get(v___x_1938_, 7);
v_infoState_1946_ = lean_ctor_get(v___x_1938_, 8);
v_snapshotTasks_1947_ = lean_ctor_get(v___x_1938_, 9);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_1938_, 5);
lean_dec(v_unused_2071_);
v___x_1949_ = v___x_1938_;
v_isShared_1950_ = v_isSharedCheck_2070_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snapshotTasks_1947_);
lean_inc(v_infoState_1946_);
lean_inc(v_messages_1945_);
lean_inc(v_recordedDeps_1944_);
lean_inc(v_traceState_1943_);
lean_inc(v_auxDeclNGen_1942_);
lean_inc(v_ngen_1941_);
lean_inc(v_nextMacroScope_1940_);
lean_inc(v_env_1939_);
lean_dec(v___x_1938_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2070_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1951_ = 1;
lean_inc_ref(v___y_1908_);
v___x_1952_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___y_1908_, v_env_1939_, v___y_1909_, v___y_1906_, v___y_1911_, v___x_1951_);
v___x_1953_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 5, v___x_1953_);
lean_ctor_set(v___x_1949_, 0, v___x_1952_);
v___x_1955_ = v___x_1949_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_nextMacroScope_1940_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_ngen_1941_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_auxDeclNGen_1942_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_traceState_1943_);
lean_ctor_set(v_reuseFailAlloc_2069_, 5, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2069_, 6, v_recordedDeps_1944_);
lean_ctor_set(v_reuseFailAlloc_2069_, 7, v_messages_1945_);
lean_ctor_set(v_reuseFailAlloc_2069_, 8, v_infoState_1946_);
lean_ctor_set(v_reuseFailAlloc_2069_, 9, v_snapshotTasks_1947_);
v___x_1955_ = v_reuseFailAlloc_2069_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_mctx_1958_; lean_object* v_zetaDeltaFVarIds_1959_; lean_object* v_postponed_1960_; lean_object* v_diag_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2067_; 
v___x_1956_ = lean_st_ref_put(v___y_1917_, v___x_1955_);
v___x_1957_ = lean_st_ref_take(v___y_1915_);
v_mctx_1958_ = lean_ctor_get(v___x_1957_, 0);
v_zetaDeltaFVarIds_1959_ = lean_ctor_get(v___x_1957_, 2);
v_postponed_1960_ = lean_ctor_get(v___x_1957_, 3);
v_diag_1961_ = lean_ctor_get(v___x_1957_, 4);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v___x_1957_, 1);
lean_dec(v_unused_2068_);
v___x_1963_ = v___x_1957_;
v_isShared_1964_ = v_isSharedCheck_2067_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_diag_1961_);
lean_inc(v_postponed_1960_);
lean_inc(v_zetaDeltaFVarIds_1959_);
lean_inc(v_mctx_1958_);
lean_dec(v___x_1957_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2067_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_mctx_1958_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_zetaDeltaFVarIds_1959_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_postponed_1960_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_diag_1961_);
v___x_1967_ = v_reuseFailAlloc_2066_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_env_1971_; lean_object* v_nextMacroScope_1972_; lean_object* v_ngen_1973_; lean_object* v_auxDeclNGen_1974_; lean_object* v_traceState_1975_; lean_object* v_recordedDeps_1976_; lean_object* v_messages_1977_; lean_object* v_infoState_1978_; lean_object* v_snapshotTasks_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2064_; 
v___x_1968_ = lean_st_ref_put(v___y_1915_, v___x_1967_);
lean_inc(v___y_1912_);
v___x_1969_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___y_1912_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v___x_1969_);
v___x_1970_ = lean_st_ref_take(v___y_1917_);
v_env_1971_ = lean_ctor_get(v___x_1970_, 0);
v_nextMacroScope_1972_ = lean_ctor_get(v___x_1970_, 1);
v_ngen_1973_ = lean_ctor_get(v___x_1970_, 2);
v_auxDeclNGen_1974_ = lean_ctor_get(v___x_1970_, 3);
v_traceState_1975_ = lean_ctor_get(v___x_1970_, 4);
v_recordedDeps_1976_ = lean_ctor_get(v___x_1970_, 6);
v_messages_1977_ = lean_ctor_get(v___x_1970_, 7);
v_infoState_1978_ = lean_ctor_get(v___x_1970_, 8);
v_snapshotTasks_1979_ = lean_ctor_get(v___x_1970_, 9);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_1970_, 5);
lean_dec(v_unused_2065_);
v___x_1981_ = v___x_1970_;
v_isShared_1982_ = v_isSharedCheck_2064_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snapshotTasks_1979_);
lean_inc(v_infoState_1978_);
lean_inc(v_messages_1977_);
lean_inc(v_recordedDeps_1976_);
lean_inc(v_traceState_1975_);
lean_inc(v_auxDeclNGen_1974_);
lean_inc(v_ngen_1973_);
lean_inc(v_nextMacroScope_1972_);
lean_inc(v_env_1971_);
lean_dec(v___x_1970_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2064_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_inc(v___y_1912_);
v___x_1983_ = l_Lean_markSparseCasesOn(v_env_1971_, v___y_1912_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 5, v___x_1953_);
lean_ctor_set(v___x_1981_, 0, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_nextMacroScope_1972_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_ngen_1973_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_auxDeclNGen_1974_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_traceState_1975_);
lean_ctor_set(v_reuseFailAlloc_2063_, 5, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2063_, 6, v_recordedDeps_1976_);
lean_ctor_set(v_reuseFailAlloc_2063_, 7, v_messages_1977_);
lean_ctor_set(v_reuseFailAlloc_2063_, 8, v_infoState_1978_);
lean_ctor_set(v_reuseFailAlloc_2063_, 9, v_snapshotTasks_1979_);
v___x_1985_ = v_reuseFailAlloc_2063_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_mctx_1988_; lean_object* v_zetaDeltaFVarIds_1989_; lean_object* v_postponed_1990_; lean_object* v_diag_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2061_; 
v___x_1986_ = lean_st_ref_put(v___y_1917_, v___x_1985_);
v___x_1987_ = lean_st_ref_take(v___y_1915_);
v_mctx_1988_ = lean_ctor_get(v___x_1987_, 0);
v_zetaDeltaFVarIds_1989_ = lean_ctor_get(v___x_1987_, 2);
v_postponed_1990_ = lean_ctor_get(v___x_1987_, 3);
v_diag_1991_ = lean_ctor_get(v___x_1987_, 4);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_1987_, 1);
lean_dec(v_unused_2062_);
v___x_1993_ = v___x_1987_;
v_isShared_1994_ = v_isSharedCheck_2061_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_diag_1991_);
lean_inc(v_postponed_1990_);
lean_inc(v_zetaDeltaFVarIds_1989_);
lean_inc(v_mctx_1988_);
lean_dec(v___x_1987_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2061_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_1965_);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_mctx_1988_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_zetaDeltaFVarIds_1989_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_postponed_1990_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_diag_1991_);
v___x_1996_ = v_reuseFailAlloc_2060_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v_env_1999_; lean_object* v_nextMacroScope_2000_; lean_object* v_ngen_2001_; lean_object* v_auxDeclNGen_2002_; lean_object* v_traceState_2003_; lean_object* v_recordedDeps_2004_; lean_object* v_messages_2005_; lean_object* v_infoState_2006_; lean_object* v_snapshotTasks_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2058_; 
v___x_1997_ = lean_st_ref_put(v___y_1915_, v___x_1996_);
v___x_1998_ = lean_st_ref_take(v___y_1917_);
v_env_1999_ = lean_ctor_get(v___x_1998_, 0);
v_nextMacroScope_2000_ = lean_ctor_get(v___x_1998_, 1);
v_ngen_2001_ = lean_ctor_get(v___x_1998_, 2);
v_auxDeclNGen_2002_ = lean_ctor_get(v___x_1998_, 3);
v_traceState_2003_ = lean_ctor_get(v___x_1998_, 4);
v_recordedDeps_2004_ = lean_ctor_get(v___x_1998_, 6);
v_messages_2005_ = lean_ctor_get(v___x_1998_, 7);
v_infoState_2006_ = lean_ctor_get(v___x_1998_, 8);
v_snapshotTasks_2007_ = lean_ctor_get(v___x_1998_, 9);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v___x_1998_, 5);
lean_dec(v_unused_2059_);
v___x_2009_ = v___x_1998_;
v_isShared_2010_ = v_isSharedCheck_2058_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snapshotTasks_2007_);
lean_inc(v_infoState_2006_);
lean_inc(v_messages_2005_);
lean_inc(v_recordedDeps_2004_);
lean_inc(v_traceState_2003_);
lean_inc(v_auxDeclNGen_2002_);
lean_inc(v_ngen_2001_);
lean_inc(v_nextMacroScope_2000_);
lean_inc(v_env_1999_);
lean_dec(v___x_1998_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2058_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_numParams_2011_; lean_object* v_numIndices_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v_numParams_2011_ = lean_ctor_get(v___y_1910_, 1);
lean_inc(v_numParams_2011_);
v_numIndices_2012_ = lean_ctor_get(v___y_1910_, 2);
lean_inc(v_numIndices_2012_);
lean_dec_ref(v___y_1910_);
v___x_2013_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_add(v_numParams_2011_, v___x_2014_);
lean_dec(v_numParams_2011_);
v___x_2016_ = lean_nat_add(v___x_2015_, v_numIndices_2012_);
lean_dec(v_numIndices_2012_);
lean_dec(v___x_2015_);
v___x_2017_ = lean_nat_add(v___x_2016_, v___x_2014_);
v___x_2018_ = lean_array_get_size(v_ctors_1891_);
v___x_2019_ = lean_nat_add(v___x_2017_, v___x_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_nat_add(v___x_2019_, v___x_2014_);
lean_dec(v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2021_, 0, v_indName_1890_);
lean_ctor_set(v___x_2021_, 1, v___x_2016_);
lean_ctor_set(v___x_2021_, 2, v___x_2020_);
lean_ctor_set(v___x_2021_, 3, v_ctors_1891_);
lean_inc(v___y_1912_);
v___x_2022_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2013_, v_env_1999_, v___y_1912_, v___x_2021_, v___y_1913_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 5, v___x_1953_);
lean_ctor_set(v___x_2009_, 0, v___x_2022_);
v___x_2024_ = v___x_2009_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_nextMacroScope_2000_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_ngen_2001_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_auxDeclNGen_2002_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_traceState_2003_);
lean_ctor_set(v_reuseFailAlloc_2057_, 5, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2057_, 6, v_recordedDeps_2004_);
lean_ctor_set(v_reuseFailAlloc_2057_, 7, v_messages_2005_);
lean_ctor_set(v_reuseFailAlloc_2057_, 8, v_infoState_2006_);
lean_ctor_set(v_reuseFailAlloc_2057_, 9, v_snapshotTasks_2007_);
v___x_2024_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v_mctx_2027_; lean_object* v_zetaDeltaFVarIds_2028_; lean_object* v_postponed_2029_; lean_object* v_diag_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2055_; 
v___x_2025_ = lean_st_ref_put(v___y_1917_, v___x_2024_);
v___x_2026_ = lean_st_ref_take(v___y_1915_);
v_mctx_2027_ = lean_ctor_get(v___x_2026_, 0);
v_zetaDeltaFVarIds_2028_ = lean_ctor_get(v___x_2026_, 2);
v_postponed_2029_ = lean_ctor_get(v___x_2026_, 3);
v_diag_2030_ = lean_ctor_get(v___x_2026_, 4);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v___x_2026_, 1);
lean_dec(v_unused_2056_);
v___x_2032_ = v___x_2026_;
v_isShared_2033_ = v_isSharedCheck_2055_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_diag_2030_);
lean_inc(v_postponed_2029_);
lean_inc(v_zetaDeltaFVarIds_2028_);
lean_inc(v_mctx_2027_);
lean_dec(v___x_2026_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2055_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_1965_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_mctx_2027_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_zetaDeltaFVarIds_2028_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_postponed_2029_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_diag_2030_);
v___x_2035_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_st_ref_put(v___y_1915_, v___x_2035_);
lean_inc(v___y_1912_);
v___x_2037_ = l_Lean_enableRealizationsForConst(v___y_1912_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v___x_2037_, 0);
lean_dec(v_unused_2045_);
v___x_2039_ = v___x_2037_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v___x_2037_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___y_1912_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___y_1912_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v___y_1912_);
v_a_2046_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2037_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2037_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
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
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2072_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_1937_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_1937_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_1926_);
lean_dec_ref_known(v___x_1918_, 2);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2082_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_1927_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_1927_);
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
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref_known(v___x_1918_, 2);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2090_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_1925_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_1925_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v___x_1918_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v___x_2098_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__0, &l_Lean_Meta_mkSparseCasesOn___closed__0_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__0);
v___x_2099_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v___x_2098_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_2099_;
}
}
v___jp_2100_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_inc(v_indName_1890_);
v___x_2113_ = l_Lean_mkCasesOnName(v_indName_1890_);
lean_inc(v___x_2113_);
v___x_2114_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v___x_2113_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_toConstantVal_2115_; lean_object* v_a_2116_; lean_object* v_numParams_2117_; lean_object* v_numIndices_2118_; lean_object* v_ctors_2119_; lean_object* v_levelParams_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_toConstantVal_2115_ = lean_ctor_get(v___y_2101_, 0);
v_a_2116_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2114_, 1);
v_numParams_2117_ = lean_ctor_get(v___y_2101_, 1);
lean_inc(v_numParams_2117_);
v_numIndices_2118_ = lean_ctor_get(v___y_2101_, 2);
lean_inc(v_numIndices_2118_);
v_ctors_2119_ = lean_ctor_get(v___y_2101_, 4);
lean_inc(v_ctors_2119_);
v_levelParams_2120_ = lean_ctor_get(v_toConstantVal_2115_, 1);
lean_inc(v_indName_1890_);
v___x_2121_ = l_Lean_mkCtorIdxName(v_indName_1890_);
v___x_2122_ = l_Lean_ConstantInfo_levelParams(v_a_2116_);
v___x_2123_ = l_List_lengthTR___redArg(v___x_2122_);
lean_dec(v___x_2122_);
v___x_2124_ = l_List_lengthTR___redArg(v_levelParams_2120_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v___x_2124_, v___x_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_nat_dec_eq(v___x_2123_, v___x_2126_);
lean_dec(v___x_2126_);
lean_dec(v___x_2123_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v___x_2121_);
lean_dec(v_ctors_2119_);
lean_dec(v_numIndices_2118_);
lean_dec(v_numParams_2117_);
lean_dec(v_a_2116_);
lean_dec(v___y_2108_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v___x_2128_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_2129_ = l_Lean_MessageData_ofConstName(v___x_2113_, v___x_2127_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2132_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_inc(v_a_2116_);
v___y_1899_ = v_numParams_2117_;
v___y_1900_ = v___x_2113_;
v___y_1901_ = v___x_2121_;
v___y_1902_ = v_a_2116_;
v___y_1903_ = v_numIndices_2118_;
v___y_1904_ = v_ctors_2119_;
v___y_1905_ = v___y_2102_;
v___y_1906_ = v___y_2103_;
v___y_1907_ = v_a_2116_;
v___y_1908_ = v___y_2104_;
v___y_1909_ = v___y_2105_;
v___y_1910_ = v___y_2101_;
v___y_1911_ = v___y_2106_;
v___y_1912_ = v___y_2108_;
v___y_1913_ = v___y_2107_;
v___y_1914_ = v___y_2109_;
v___y_1915_ = v___y_2110_;
v___y_1916_ = v___y_2111_;
v___y_1917_ = v___y_2112_;
goto v___jp_1898_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v___x_2113_);
lean_dec(v___y_2108_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2142_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2114_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2114_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v_asyncMode_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2155_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2156_ = lean_ctor_get(v___x_2155_, 2);
lean_inc_ref(v_ctors_1891_);
lean_inc(v_indName_1890_);
v___x_2157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2157_, 0, v_indName_1890_);
lean_ctor_set(v___x_2157_, 1, v_ctors_1891_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*2, v___y_2154_);
v___x_2158_ = lean_box(0);
v___x_2159_ = 0;
v___x_2160_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2150_, v___x_2155_, v_env_2152_, v_asyncMode_2156_, v___x_2158_, v___x_2159_);
v___x_2161_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2160_, v___x_2157_);
lean_dec(v___x_2160_);
if (lean_obj_tag(v___x_2161_) == 1)
{
lean_object* v_val_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref_known(v___x_2157_, 2);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_val_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_val_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 0);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_val_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v_a_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; 
lean_dec(v___x_2161_);
v___x_2170_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__5));
v___x_2171_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2170_, v_a_1895_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc_n(v_a_2172_, 2);
lean_dec_ref(v___x_2171_);
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2173_, 0, v___x_2157_);
lean_closure_set(v___f_2173_, 1, v_a_2172_);
lean_inc(v_indName_1890_);
v___x_2174_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_indName_1890_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; size_t v_sz_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = lean_box(0);
v_sz_2177_ = lean_array_size(v_ctors_1891_);
v___x_2178_ = ((size_t)0ULL);
lean_inc(v_indName_1890_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_2175_, v_indName_1890_, v_ctors_1891_, v_sz_2177_, v___x_2178_, v___x_2176_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_ctors_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
lean_dec_ref_known(v___x_2179_, 1);
v_ctors_2180_ = lean_ctor_get(v_a_2175_, 4);
v___x_2181_ = lean_array_get_size(v_ctors_1891_);
v___x_2182_ = l_List_lengthTR___redArg(v_ctors_2180_);
v___x_2183_ = lean_nat_dec_eq(v___x_2181_, v___x_2182_);
lean_dec(v___x_2182_);
if (v___x_2183_ == 0)
{
v___y_2101_ = v_a_2175_;
v___y_2102_ = v___x_2159_;
v___y_2103_ = v_asyncMode_2156_;
v___y_2104_ = v___x_2155_;
v___y_2105_ = v___f_2173_;
v___y_2106_ = v___x_2158_;
v___y_2107_ = v___x_2159_;
v___y_2108_ = v_a_2172_;
v___y_2109_ = v_a_1892_;
v___y_2110_ = v_a_1893_;
v___y_2111_ = v_a_1894_;
v___y_2112_ = v_a_1895_;
goto v___jp_2100_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2175_);
lean_dec_ref(v___f_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v___x_2184_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__7, &l_Lean_Meta_mkSparseCasesOn___closed__7_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__7);
v___x_2185_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2184_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2175_);
lean_dec_ref(v___f_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2194_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2179_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2179_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v___f_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_ctors_1891_);
lean_dec(v_indName_1890_);
v_a_2202_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2174_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2174_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkSparseCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1890_ = stack[0].m_obj;
lean_object* v_ctors_1891_ = stack[1].m_obj;
lean_object* v_a_1892_ = stack[2].m_obj;
lean_object* v_a_1893_ = stack[3].m_obj;
lean_object* v_a_1894_ = stack[4].m_obj;
lean_object* v_a_1895_ = stack[5].m_obj;
lean_object* v_res_2214_;
v_res_2214_ = l_Lean_Meta_mkSparseCasesOn(v_indName_1890_, v_ctors_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
stack->m_obj
 = v_res_2214_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2215_, lean_object* v_ctors_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2215_, v_ctors_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2227_, v_x_2228_, v_x_2229_);
lean_dec_ref(v_x_2229_);
lean_dec_ref(v_x_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object* v_00_u03b1_2236_, lean_object* v_name_2237_, uint8_t v_bi_2238_, lean_object* v_type_2239_, lean_object* v_k_2240_, uint8_t v_kind_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_2237_, v_bi_2238_, v_type_2239_, v_k_2240_, v_kind_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2237_ = stack[1].m_obj;
uint8_t v_bi_2238_ = stack[2].m_num;
lean_object* v_type_2239_ = stack[3].m_obj;
lean_object* v_k_2240_ = stack[4].m_obj;
uint8_t v_kind_2241_ = stack[5].m_num;
lean_object* v___y_2242_ = stack[6].m_obj;
lean_object* v___y_2243_ = stack[7].m_obj;
lean_object* v___y_2244_ = stack[8].m_obj;
lean_object* v___y_2245_ = stack[9].m_obj;
lean_object* v_res_2248_;
v_res_2248_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_box(0), v_name_2237_, v_bi_2238_, v_type_2239_, v_k_2240_, v_kind_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
stack->m_obj
 = v_res_2248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_name_2250_, lean_object* v_bi_2251_, lean_object* v_type_2252_, lean_object* v_k_2253_, lean_object* v_kind_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_bi_boxed_2260_; uint8_t v_kind_boxed_2261_; lean_object* v_res_2262_; 
v_bi_boxed_2260_ = lean_unbox(v_bi_2251_);
v_kind_boxed_2261_ = lean_unbox(v_kind_2254_);
v_res_2262_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(v_00_u03b1_2249_, v_name_2250_, v_bi_boxed_2260_, v_type_2252_, v_k_2253_, v_kind_boxed_2261_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2262_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_00_u03b1_2263_, lean_object* v_name_2264_, lean_object* v_type_2265_, lean_object* v_k_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_2264_, v_type_2265_, v_k_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2272_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2264_ = stack[1].m_obj;
lean_object* v_type_2265_ = stack[2].m_obj;
lean_object* v_k_2266_ = stack[3].m_obj;
lean_object* v___y_2267_ = stack[4].m_obj;
lean_object* v___y_2268_ = stack[5].m_obj;
lean_object* v___y_2269_ = stack[6].m_obj;
lean_object* v___y_2270_ = stack[7].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_box(0), v_name_2264_, v_type_2265_, v_k_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_name_2275_, lean_object* v_type_2276_, lean_object* v_k_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_00_u03b1_2274_, v_name_2275_, v_type_2276_, v_k_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object* v_00_u03b1_2284_, lean_object* v_msg_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2285_ = stack[1].m_obj;
lean_object* v___y_2286_ = stack[2].m_obj;
lean_object* v___y_2287_ = stack[3].m_obj;
lean_object* v___y_2288_ = stack[4].m_obj;
lean_object* v___y_2289_ = stack[5].m_obj;
lean_object* v_res_2292_;
v_res_2292_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_box(0), v_msg_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
stack->m_obj
 = v_res_2292_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(v_00_u03b1_2293_, v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2300_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object* v_declName_2301_, uint8_t v_s_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_2301_, v_s_2302_, v___y_2304_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2301_ = stack[0].m_obj;
uint8_t v_s_2302_ = stack[1].m_num;
lean_object* v___y_2303_ = stack[2].m_obj;
lean_object* v___y_2304_ = stack[3].m_obj;
lean_object* v___y_2305_ = stack[4].m_obj;
lean_object* v___y_2306_ = stack[5].m_obj;
lean_object* v_res_2309_;
v_res_2309_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(v_declName_2301_, v_s_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
stack->m_obj
 = v_res_2309_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object* v_declName_2310_, lean_object* v_s_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v_s_boxed_2317_; lean_object* v_res_2318_; 
v_s_boxed_2317_ = lean_unbox(v_s_2311_);
v_res_2318_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(v_declName_2310_, v_s_boxed_2317_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2318_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2319_, lean_object* v_x_2320_, size_t v_x_2321_, lean_object* v_x_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2320_, v_x_2321_, v_x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2320_ = stack[1].m_obj;
size_t v_x_2321_ = stack[2].m_num;
lean_object* v_x_2322_ = stack[3].m_obj;
lean_object* v_res_2324_;
v_res_2324_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_box(0), v_x_2320_, v_x_2321_, v_x_2322_);
stack->m_obj
 = v_res_2324_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
size_t v_x_26418__boxed_2329_; lean_object* v_res_2330_; 
v_x_26418__boxed_2329_ = lean_unbox_usize(v_x_2327_);
lean_dec(v_x_2327_);
v_res_2330_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2325_, v_x_2326_, v_x_26418__boxed_2329_, v_x_2328_);
lean_dec_ref(v_x_2328_);
lean_dec_ref(v_x_2326_);
return v_res_2330_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2331_, lean_object* v_x_2332_, size_t v_x_2333_, size_t v_x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2332_, v_x_2333_, v_x_2334_, v_x_2335_, v_x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2332_ = stack[1].m_obj;
size_t v_x_2333_ = stack[2].m_num;
size_t v_x_2334_ = stack[3].m_num;
lean_object* v_x_2335_ = stack[4].m_obj;
lean_object* v_x_2336_ = stack[5].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_box(0), v_x_2332_, v_x_2333_, v_x_2334_, v_x_2335_, v_x_2336_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
size_t v_x_26436__boxed_2345_; size_t v_x_26437__boxed_2346_; lean_object* v_res_2347_; 
v_x_26436__boxed_2345_ = lean_unbox_usize(v_x_2341_);
lean_dec(v_x_2341_);
v_x_26437__boxed_2346_ = lean_unbox_usize(v_x_2342_);
lean_dec(v_x_2342_);
v_res_2347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2339_, v_x_2340_, v_x_26436__boxed_2345_, v_x_26437__boxed_2346_, v_x_2343_, v_x_2344_);
return v_res_2347_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object* v_00_u03b1_2348_, lean_object* v_constName_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2349_ = stack[1].m_obj;
lean_object* v___y_2350_ = stack[2].m_obj;
lean_object* v___y_2351_ = stack[3].m_obj;
lean_object* v___y_2352_ = stack[4].m_obj;
lean_object* v___y_2353_ = stack[5].m_obj;
lean_object* v_res_2356_;
v_res_2356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_box(0), v_constName_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
stack->m_obj
 = v_res_2356_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2357_, lean_object* v_constName_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(v_00_u03b1_2357_, v_constName_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_k_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_2366_, v_vals_2367_, v_i_2369_, v_k_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_heq_2375_, lean_object* v_i_2376_, lean_object* v_k_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(v_00_u03b2_2372_, v_keys_2373_, v_vals_2374_, v_heq_2375_, v_i_2376_, v_k_2377_);
lean_dec_ref(v_k_2377_);
lean_dec_ref(v_vals_2374_);
lean_dec_ref(v_keys_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2379_, lean_object* v_n_2380_, lean_object* v_k_2381_, lean_object* v_v_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_n_2380_, v_k_2381_, v_v_2382_);
return v___x_2383_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object* v_00_u03b2_2384_, size_t v_depth_2385_, lean_object* v_keys_2386_, lean_object* v_vals_2387_, lean_object* v_heq_2388_, lean_object* v_i_2389_, lean_object* v_entries_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_2385_, v_keys_2386_, v_vals_2387_, v_i_2389_, v_entries_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2385_ = stack[1].m_num;
lean_object* v_keys_2386_ = stack[2].m_obj;
lean_object* v_vals_2387_ = stack[3].m_obj;
lean_object* v_i_2389_ = stack[5].m_obj;
lean_object* v_entries_2390_ = stack[6].m_obj;
lean_object* v_res_2392_;
v_res_2392_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_box(0), v_depth_2385_, v_keys_2386_, v_vals_2387_, lean_box(0), v_i_2389_, v_entries_2390_);
stack->m_obj
 = v_res_2392_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object* v_00_u03b2_2393_, lean_object* v_depth_2394_, lean_object* v_keys_2395_, lean_object* v_vals_2396_, lean_object* v_heq_2397_, lean_object* v_i_2398_, lean_object* v_entries_2399_){
_start:
{
size_t v_depth_boxed_2400_; lean_object* v_res_2401_; 
v_depth_boxed_2400_ = lean_unbox_usize(v_depth_2394_);
lean_dec(v_depth_2394_);
v_res_2401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(v_00_u03b2_2393_, v_depth_boxed_2400_, v_keys_2395_, v_vals_2396_, v_heq_2397_, v_i_2398_, v_entries_2399_);
lean_dec_ref(v_vals_2396_);
lean_dec_ref(v_keys_2395_);
return v_res_2401_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object* v_00_u03b1_2402_, lean_object* v_ref_2403_, lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_2403_, v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2403_ = stack[1].m_obj;
lean_object* v_constName_2404_ = stack[2].m_obj;
lean_object* v___y_2405_ = stack[3].m_obj;
lean_object* v___y_2406_ = stack[4].m_obj;
lean_object* v___y_2407_ = stack[5].m_obj;
lean_object* v___y_2408_ = stack[6].m_obj;
lean_object* v_res_2411_;
v_res_2411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_box(0), v_ref_2403_, v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object* v_00_u03b1_2412_, lean_object* v_ref_2413_, lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(v_00_u03b1_2412_, v_ref_2413_, v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_ref_2413_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object* v_00_u03b2_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_x_2422_, v_x_2423_, v_x_2424_, v_x_2425_);
return v___x_2426_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object* v_00_u03b1_2427_, lean_object* v_ref_2428_, lean_object* v_msg_2429_, lean_object* v_declHint_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_2428_, v_msg_2429_, v_declHint_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2428_ = stack[1].m_obj;
lean_object* v_msg_2429_ = stack[2].m_obj;
lean_object* v_declHint_2430_ = stack[3].m_obj;
lean_object* v___y_2431_ = stack[4].m_obj;
lean_object* v___y_2432_ = stack[5].m_obj;
lean_object* v___y_2433_ = stack[6].m_obj;
lean_object* v___y_2434_ = stack[7].m_obj;
lean_object* v_res_2437_;
v_res_2437_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_box(0), v_ref_2428_, v_msg_2429_, v_declHint_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
stack->m_obj
 = v_res_2437_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_ref_2439_, lean_object* v_msg_2440_, lean_object* v_declHint_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(v_00_u03b1_2438_, v_ref_2439_, v_msg_2440_, v_declHint_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v_ref_2439_);
return v_res_2447_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object* v_msg_2448_, lean_object* v_declHint_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_2448_, v_declHint_2449_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2448_ = stack[0].m_obj;
lean_object* v_declHint_2449_ = stack[1].m_obj;
lean_object* v___y_2450_ = stack[2].m_obj;
lean_object* v___y_2451_ = stack[3].m_obj;
lean_object* v___y_2452_ = stack[4].m_obj;
lean_object* v___y_2453_ = stack[5].m_obj;
lean_object* v_res_2456_;
v_res_2456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(v_msg_2448_, v_declHint_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
stack->m_obj
 = v_res_2456_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object* v_msg_2457_, lean_object* v_declHint_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(v_msg_2457_, v_declHint_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2464_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object* v_00_u03b1_2465_, lean_object* v_ref_2466_, lean_object* v_msg_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_2466_, v_msg_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2466_ = stack[1].m_obj;
lean_object* v_msg_2467_ = stack[2].m_obj;
lean_object* v___y_2468_ = stack[3].m_obj;
lean_object* v___y_2469_ = stack[4].m_obj;
lean_object* v___y_2470_ = stack[5].m_obj;
lean_object* v___y_2471_ = stack[6].m_obj;
lean_object* v_res_2474_;
v_res_2474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_box(0), v_ref_2466_, v_msg_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
stack->m_obj
 = v_res_2474_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_ref_2476_, lean_object* v_msg_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(v_00_u03b1_2475_, v_ref_2476_, v_msg_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v_ref_2476_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2484_, lean_object* v_sparseCasesOnName_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v_toEnvExtension_2487_; lean_object* v_asyncMode_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2486_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2487_ = lean_ctor_get(v___x_2486_, 0);
v_asyncMode_2488_ = lean_ctor_get(v_toEnvExtension_2487_, 2);
v___x_2489_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2490_ = 0;
v___x_2491_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2489_, v___x_2486_, v_env_2484_, v_sparseCasesOnName_2485_, v_asyncMode_2488_, v___x_2490_);
return v___x_2491_;
}
}
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_env_2497_; lean_object* v___x_2498_; lean_object* v_toEnvExtension_2499_; lean_object* v_asyncMode_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2495_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2496_ = lean_st_ref_get(v_a_2493_);
v_env_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc_ref(v_env_2497_);
lean_dec(v___x_2496_);
v___x_2498_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2499_ = lean_ctor_get(v___x_2498_, 0);
v_asyncMode_2500_ = lean_ctor_get(v_toEnvExtension_2499_, 2);
v___x_2501_ = 0;
v___x_2502_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2495_, v___x_2498_, v_env_2497_, v_sparseCasesOnName_2492_, v_asyncMode_2500_, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT void l_Lean_Meta_getSparseCasesOnInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sparseCasesOnName_2492_ = stack[0].m_obj;
lean_object* v_a_2493_ = stack[1].m_obj;
lean_object* v_res_2504_;
v_res_2504_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2492_, v_a_2493_);
stack->m_obj
 = v_res_2504_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2505_, v_a_2506_);
lean_dec(v_a_2506_);
return v_res_2508_;
}
}
lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2509_, v_a_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT void l_Lean_Meta_getSparseCasesOnInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_sparseCasesOnName_2509_ = stack[0].m_obj;
lean_object* v_a_2510_ = stack[1].m_obj;
lean_object* v_a_2511_ = stack[2].m_obj;
lean_object* v_res_2514_;
v_res_2514_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2509_, v_a_2510_, v_a_2511_);
stack->m_obj
 = v_res_2514_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
return v_res_2519_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
