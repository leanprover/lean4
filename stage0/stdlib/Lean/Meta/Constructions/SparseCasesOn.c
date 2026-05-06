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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_mkHasNotBit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
static const lean_array_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SparseCasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 142, 211, 52, 27, 176, 89, 6)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 38, 184, 128, 76, 32, 215, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 79, 91, 86, 222, 171, 161, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 83, 47, 52, 170, 238, 223, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sparseCasesOnInfoExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 231, 162, 79, 58, 254, 239, 178)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkSparseCasesOn: constructor "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is not a constructor of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Constructions.SparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.mkSparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__2;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mkSparseCasesOn: unexpected number of universe parameters in `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__4;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__5;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_sparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__6 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(111, 99, 43, 146, 60, 255, 155, 135)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__7 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__7_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "mkSparseCasesOn: requested casesOn combinator is not sparse"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__8 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__8_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
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
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object* v_xs_12_, lean_object* v_ys_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_12_, v_ys_13_, v_x_14_);
lean_dec_ref(v_ys_13_);
lean_dec_ref(v_xs_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_indName_19_; lean_object* v_ctors_20_; uint8_t v_isPrivate_21_; lean_object* v_indName_22_; lean_object* v_ctors_23_; uint8_t v_isPrivate_24_; uint8_t v___x_25_; 
v_indName_19_ = lean_ctor_get(v_x_17_, 0);
v_ctors_20_ = lean_ctor_get(v_x_17_, 1);
v_isPrivate_21_ = lean_ctor_get_uint8(v_x_17_, sizeof(void*)*2);
v_indName_22_ = lean_ctor_get(v_x_18_, 0);
v_ctors_23_ = lean_ctor_get(v_x_18_, 1);
v_isPrivate_24_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*2);
v___x_25_ = lean_name_eq(v_indName_19_, v_indName_22_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_array_get_size(v_ctors_20_);
v___x_27_ = lean_array_get_size(v_ctors_23_);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_20_, v_ctors_23_, v___x_26_);
if (v___x_29_ == 0)
{
return v___x_29_;
}
else
{
if (v_isPrivate_21_ == 0)
{
if (v_isPrivate_24_ == 0)
{
return v___x_29_;
}
else
{
return v_isPrivate_21_;
}
}
else
{
return v_isPrivate_24_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object* v_xs_34_, lean_object* v_ys_35_, lean_object* v_hsz_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_34_, v_ys_35_, v_x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object* v_xs_40_, lean_object* v_ys_41_, lean_object* v_hsz_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_40_, v_ys_41_, v_hsz_42_, v_x_43_, v_x_44_);
lean_dec_ref(v_ys_41_);
lean_dec_ref(v_xs_40_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0(void){
_start:
{
lean_object* v___x_49_; uint64_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1723u);
v___x_50_ = lean_uint64_of_nat(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object* v_as_51_, size_t v_i_52_, size_t v_stop_53_, uint64_t v_b_54_){
_start:
{
uint64_t v___y_56_; uint8_t v___x_61_; 
v___x_61_ = lean_usize_dec_eq(v_i_52_, v_stop_53_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_array_uget_borrowed(v_as_51_, v_i_52_);
if (lean_obj_tag(v___x_62_) == 0)
{
uint64_t v___x_63_; 
v___x_63_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0);
v___y_56_ = v___x_63_;
goto v___jp_55_;
}
else
{
uint64_t v_hash_64_; 
v_hash_64_ = lean_ctor_get_uint64(v___x_62_, sizeof(void*)*2);
v___y_56_ = v_hash_64_;
goto v___jp_55_;
}
}
else
{
return v_b_54_;
}
v___jp_55_:
{
uint64_t v___x_57_; size_t v___x_58_; size_t v___x_59_; 
v___x_57_ = lean_uint64_mix_hash(v_b_54_, v___y_56_);
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_52_, v___x_58_);
v_i_52_ = v___x_59_;
v_b_54_ = v___x_57_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; uint64_t v_b_boxed_71_; uint64_t v_res_72_; lean_object* v_r_73_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_b_boxed_71_ = lean_unbox_uint64(v_b_68_);
lean_dec_ref(v_b_68_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_65_, v_i_boxed_69_, v_stop_boxed_70_, v_b_boxed_71_);
lean_dec_ref(v_as_65_);
v_r_73_ = lean_box_uint64(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object* v_x_74_){
_start:
{
lean_object* v_indName_75_; lean_object* v_ctors_76_; uint8_t v_isPrivate_77_; uint64_t v___y_79_; uint64_t v___y_80_; uint64_t v___x_86_; uint64_t v___y_88_; 
v_indName_75_ = lean_ctor_get(v_x_74_, 0);
v_ctors_76_ = lean_ctor_get(v_x_74_, 1);
v_isPrivate_77_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*2);
v___x_86_ = 0ULL;
if (lean_obj_tag(v_indName_75_) == 0)
{
uint64_t v___x_101_; 
v___x_101_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0);
v___y_88_ = v___x_101_;
goto v___jp_87_;
}
else
{
uint64_t v_hash_102_; 
v_hash_102_ = lean_ctor_get_uint64(v_indName_75_, sizeof(void*)*2);
v___y_88_ = v_hash_102_;
goto v___jp_87_;
}
v___jp_78_:
{
uint64_t v___x_81_; 
v___x_81_ = lean_uint64_mix_hash(v___y_79_, v___y_80_);
if (v_isPrivate_77_ == 0)
{
uint64_t v___x_82_; uint64_t v___x_83_; 
v___x_82_ = 13ULL;
v___x_83_ = lean_uint64_mix_hash(v___x_81_, v___x_82_);
return v___x_83_;
}
else
{
uint64_t v___x_84_; uint64_t v___x_85_; 
v___x_84_ = 11ULL;
v___x_85_ = lean_uint64_mix_hash(v___x_81_, v___x_84_);
return v___x_85_;
}
}
v___jp_87_:
{
uint64_t v___x_89_; uint64_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_89_ = lean_uint64_mix_hash(v___x_86_, v___y_88_);
v___x_90_ = 7ULL;
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_array_get_size(v_ctors_76_);
v___x_93_ = lean_nat_dec_lt(v___x_91_, v___x_92_);
if (v___x_93_ == 0)
{
v___y_79_ = v___x_89_;
v___y_80_ = v___x_90_;
goto v___jp_78_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_92_);
if (v___x_94_ == 0)
{
if (v___x_93_ == 0)
{
v___y_79_ = v___x_89_;
v___y_80_ = v___x_90_;
goto v___jp_78_;
}
else
{
size_t v___x_95_; size_t v___x_96_; uint64_t v___x_97_; 
v___x_95_ = ((size_t)0ULL);
v___x_96_ = lean_usize_of_nat(v___x_92_);
v___x_97_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_76_, v___x_95_, v___x_96_, v___x_90_);
v___y_79_ = v___x_89_;
v___y_80_ = v___x_97_;
goto v___jp_78_;
}
}
else
{
size_t v___x_98_; size_t v___x_99_; uint64_t v___x_100_; 
v___x_98_ = ((size_t)0ULL);
v___x_99_ = lean_usize_of_nat(v___x_92_);
v___x_100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_76_, v___x_98_, v___x_99_, v___x_90_);
v___y_79_ = v___x_89_;
v___y_80_ = v___x_100_;
goto v___jp_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object* v_x_103_){
_start:
{
uint64_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_103_);
lean_dec_ref(v_x_103_);
v_r_105_ = lean_box_uint64(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(lean_object* v___x_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object* v___x_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(v___x_111_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_117_; lean_object* v___f_118_; 
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_118_, 0, v___x_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___f_120_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_box(1);
v___x_123_ = l_Lean_registerEnvExtension___redArg(v___f_120_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(lean_object* v_env_134_, lean_object* v_n_135_, lean_object* v_x_136_){
_start:
{
uint8_t v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; 
v___x_137_ = 1;
v___x_138_ = l_Lean_Environment_setExporting(v_env_134_, v___x_137_);
v___x_139_ = 0;
v___x_140_ = l_Lean_Environment_find_x3f(v___x_138_, v_n_135_, v___x_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
return v___x_139_;
}
else
{
lean_object* v_val_141_; uint8_t v___x_142_; 
v_val_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_val_141_);
lean_dec_ref(v___x_140_);
v___x_142_ = l_Lean_ConstantInfo_hasValue(v_val_141_, v___x_139_);
lean_dec(v_val_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(lean_object* v_env_143_, lean_object* v_n_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(v_env_143_, v_n_144_, v_x_145_);
lean_dec_ref(v_x_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_k_150_; lean_object* v_v_151_; lean_object* v_l_152_; lean_object* v_r_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_k_150_ = lean_ctor_get(v_x_149_, 1);
v_v_151_ = lean_ctor_get(v_x_149_, 2);
v_l_152_ = lean_ctor_get(v_x_149_, 3);
v_r_153_ = lean_ctor_get(v_x_149_, 4);
v___x_154_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_148_, v_l_152_);
lean_inc(v_v_151_);
lean_inc(v_k_150_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_k_150_);
lean_ctor_set(v___x_155_, 1, v_v_151_);
v___x_156_ = lean_array_push(v___x_154_, v___x_155_);
v_init_148_ = v___x_156_;
v_x_149_ = v_r_153_;
goto _start;
}
else
{
return v_init_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_158_, v_x_159_);
lean_dec(v_x_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(lean_object* v_env_163_, lean_object* v_s_164_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v_all_167_; lean_object* v___x_168_; lean_object* v_exported_169_; lean_object* v___x_170_; 
v___f_165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_165_, 0, v_env_163_);
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_));
v_all_167_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v___x_166_, v_s_164_);
v___x_168_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_165_, v_s_164_);
v_exported_169_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v___x_166_, v___x_168_);
lean_dec(v___x_168_);
lean_inc_ref(v_exported_169_);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v_exported_169_);
lean_ctor_set(v___x_170_, 1, v_exported_169_);
lean_ctor_set(v___x_170_, 2, v_all_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___f_208_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_));
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_));
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_));
v___x_211_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_209_, v___x_210_, v___f_208_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_();
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0(lean_object* v_init_214_, lean_object* v_t_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_214_, v_t_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_217_, lean_object* v_t_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0(v_init_217_, v_t_218_);
lean_dec(v_t_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object* v_kind_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_auxDeclNGen_224_; lean_object* v___x_225_; lean_object* v_env_226_; lean_object* v___x_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v_env_231_; lean_object* v_nextMacroScope_232_; lean_object* v_ngen_233_; lean_object* v_traceState_234_; lean_object* v_cache_235_; lean_object* v_messages_236_; lean_object* v_infoState_237_; lean_object* v_snapshotTasks_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_247_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_auxDeclNGen_224_ = lean_ctor_get(v___x_223_, 3);
lean_inc_ref(v_auxDeclNGen_224_);
lean_dec(v___x_223_);
v___x_225_ = lean_st_ref_get(v___y_221_);
v_env_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_226_);
lean_dec(v___x_225_);
v___x_227_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_226_, v_auxDeclNGen_224_, v_kind_220_);
v_fst_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v___x_227_, 1);
lean_inc(v_snd_229_);
lean_dec_ref(v___x_227_);
v___x_230_ = lean_st_ref_take(v___y_221_);
v_env_231_ = lean_ctor_get(v___x_230_, 0);
v_nextMacroScope_232_ = lean_ctor_get(v___x_230_, 1);
v_ngen_233_ = lean_ctor_get(v___x_230_, 2);
v_traceState_234_ = lean_ctor_get(v___x_230_, 4);
v_cache_235_ = lean_ctor_get(v___x_230_, 5);
v_messages_236_ = lean_ctor_get(v___x_230_, 6);
v_infoState_237_ = lean_ctor_get(v___x_230_, 7);
v_snapshotTasks_238_ = lean_ctor_get(v___x_230_, 8);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v___x_230_, 3);
lean_dec(v_unused_248_);
v___x_240_ = v___x_230_;
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snapshotTasks_238_);
lean_inc(v_infoState_237_);
lean_inc(v_messages_236_);
lean_inc(v_cache_235_);
lean_inc(v_traceState_234_);
lean_inc(v_ngen_233_);
lean_inc(v_nextMacroScope_232_);
lean_inc(v_env_231_);
lean_dec(v___x_230_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v_snd_229_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_env_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_nextMacroScope_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_ngen_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_snd_229_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_traceState_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_cache_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_messages_236_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_infoState_237_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_snapshotTasks_238_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_st_ref_set(v___y_221_, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_fst_228_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object* v_kind_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_249_, v___y_250_);
lean_dec(v___y_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object* v_kind_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_253_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object* v_kind_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(lean_object* v_k_267_, lean_object* v_b_268_, lean_object* v_c_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_275_ = lean_apply_7(v_k_267_, v_b_268_, v_c_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed(lean_object* v_k_276_, lean_object* v_b_277_, lean_object* v_c_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(v_k_276_, v_b_277_, v_c_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(lean_object* v_type_285_, lean_object* v_k_286_, uint8_t v_cleanupAnnotations_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___f_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___f_293_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_293_, 0, v_k_286_);
v___x_294_ = 0;
v___x_295_ = lean_box(0);
v___x_296_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_294_, v___x_295_, v_type_285_, v___f_293_, v_cleanupAnnotations_287_, v___x_294_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_296_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_296_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___boxed(lean_object* v_type_313_, lean_object* v_k_314_, lean_object* v_cleanupAnnotations_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_321_; lean_object* v_res_322_; 
v_cleanupAnnotations_boxed_321_ = lean_unbox(v_cleanupAnnotations_315_);
v_res_322_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_type_313_, v_k_314_, v_cleanupAnnotations_boxed_321_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object* v_00_u03b1_323_, lean_object* v_type_324_, lean_object* v_k_325_, uint8_t v_cleanupAnnotations_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_type_324_, v_k_325_, v_cleanupAnnotations_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object* v_00_u03b1_333_, lean_object* v_type_334_, lean_object* v_k_335_, lean_object* v_cleanupAnnotations_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_342_; lean_object* v_res_343_; 
v_cleanupAnnotations_boxed_342_ = lean_unbox(v_cleanupAnnotations_336_);
v_res_343_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_00_u03b1_333_, v_type_334_, v_k_335_, v_cleanupAnnotations_boxed_342_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object* v_name_344_, lean_object* v_levelParams_345_, lean_object* v_type_346_, lean_object* v_value_347_, lean_object* v_hints_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; uint8_t v___y_353_; uint8_t v___y_360_; lean_object* v_env_363_; uint8_t v___x_364_; 
v___x_351_ = lean_st_ref_get(v___y_349_);
v_env_363_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref_n(v_env_363_, 2);
lean_dec(v___x_351_);
v___x_364_ = l_Lean_Environment_hasUnsafe(v_env_363_, v_type_346_);
if (v___x_364_ == 0)
{
uint8_t v___x_365_; 
v___x_365_ = l_Lean_Environment_hasUnsafe(v_env_363_, v_value_347_);
v___y_360_ = v___x_365_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v_env_363_);
v___y_360_ = v___x_364_;
goto v___jp_359_;
}
v___jp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_inc(v_name_344_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v_name_344_);
lean_ctor_set(v___x_354_, 1, v_levelParams_345_);
lean_ctor_set(v___x_354_, 2, v_type_346_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v_name_344_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_357_, 0, v___x_354_);
lean_ctor_set(v___x_357_, 1, v_value_347_);
lean_ctor_set(v___x_357_, 2, v_hints_348_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*4, v___y_353_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = 1;
v___y_353_ = v___x_361_;
goto v___jp_352_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
v___y_353_ = v___x_362_;
goto v___jp_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object* v_name_366_, lean_object* v_levelParams_367_, lean_object* v_type_368_, lean_object* v_value_369_, lean_object* v_hints_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_name_366_, v_levelParams_367_, v_type_368_, v_value_369_, v_hints_370_, v___y_371_);
lean_dec(v___y_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object* v_name_374_, lean_object* v_levelParams_375_, lean_object* v_type_376_, lean_object* v_value_377_, lean_object* v_hints_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_name_374_, v_levelParams_375_, v_type_376_, v_value_377_, v_hints_378_, v___y_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object* v_name_385_, lean_object* v_levelParams_386_, lean_object* v_type_387_, lean_object* v_value_388_, lean_object* v_hints_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(v_name_385_, v_levelParams_386_, v_type_387_, v_value_388_, v_hints_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_16979__overap_404_; lean_object* v___x_405_; 
v___f_403_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0));
v___x_16979__overap_404_ = lean_panic_fn_borrowed(v___f_403_, v_msg_397_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v___y_398_);
v___x_405_ = lean_apply_5(v___x_16979__overap_404_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, lean_box(0));
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v_ks_417_; lean_object* v_vs_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_442_; 
v_ks_417_ = lean_ctor_get(v_x_413_, 0);
v_vs_418_ = lean_ctor_get(v_x_413_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_413_);
if (v_isSharedCheck_442_ == 0)
{
v___x_420_ = v_x_413_;
v_isShared_421_ = v_isSharedCheck_442_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_vs_418_);
lean_inc(v_ks_417_);
lean_dec(v_x_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_442_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_array_get_size(v_ks_417_);
v___x_423_ = lean_nat_dec_lt(v_x_414_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_x_414_);
v___x_424_ = lean_array_push(v_ks_417_, v_x_415_);
v___x_425_ = lean_array_push(v_vs_418_, v_x_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_425_);
lean_ctor_set(v___x_420_, 0, v___x_424_);
v___x_427_ = v___x_420_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v_k_x27_429_; uint8_t v___x_430_; 
v_k_x27_429_ = lean_array_fget_borrowed(v_ks_417_, v_x_414_);
v___x_430_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_415_, v_k_x27_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_432_; 
if (v_isShared_421_ == 0)
{
v___x_432_ = v___x_420_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_ks_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_vs_418_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_x_414_, v___x_433_);
lean_dec(v_x_414_);
v_x_413_ = v___x_432_;
v_x_414_ = v___x_434_;
goto _start;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = lean_array_fset(v_ks_417_, v_x_414_, v_x_415_);
v___x_438_ = lean_array_fset(v_vs_418_, v_x_414_, v_x_416_);
lean_dec(v_x_414_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_438_);
lean_ctor_set(v___x_420_, 0, v___x_437_);
v___x_440_ = v___x_420_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(lean_object* v_n_443_, lean_object* v_k_444_, lean_object* v_v_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_n_443_, v___x_446_, v_k_444_, v_v_445_);
return v___x_447_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_shift_left(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; 
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
v___x_453_ = lean_usize_sub(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object* v_x_455_, size_t v_x_456_, size_t v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v_es_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v_j_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_es_460_ = lean_ctor_get(v_x_455_, 0);
v___x_461_ = ((size_t)5ULL);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1);
v___x_464_ = lean_usize_land(v_x_456_, v___x_463_);
v_j_465_ = lean_usize_to_nat(v___x_464_);
v___x_466_ = lean_array_get_size(v_es_460_);
v___x_467_ = lean_nat_dec_lt(v_j_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec(v_j_465_);
lean_dec(v_x_459_);
lean_dec_ref(v_x_458_);
return v_x_455_;
}
else
{
lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_504_; 
lean_inc_ref(v_es_460_);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_505_);
v___x_469_ = v_x_455_;
v_isShared_470_ = v_isSharedCheck_504_;
goto v_resetjp_468_;
}
else
{
lean_dec(v_x_455_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_504_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_v_471_; lean_object* v___x_472_; lean_object* v_xs_x27_473_; lean_object* v___y_475_; 
v_v_471_ = lean_array_fget(v_es_460_, v_j_465_);
v___x_472_ = lean_box(0);
v_xs_x27_473_ = lean_array_fset(v_es_460_, v_j_465_, v___x_472_);
switch(lean_obj_tag(v_v_471_))
{
case 0:
{
lean_object* v_key_480_; lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_491_; 
v_key_480_ = lean_ctor_get(v_v_471_, 0);
v_val_481_ = lean_ctor_get(v_v_471_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_v_471_);
if (v_isSharedCheck_491_ == 0)
{
v___x_483_ = v_v_471_;
v_isShared_484_ = v_isSharedCheck_491_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_inc(v_key_480_);
lean_dec(v_v_471_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_491_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_458_, v_key_480_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_del_object(v___x_483_);
v___x_486_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_480_, v_val_481_, v_x_458_, v_x_459_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___y_475_ = v___x_487_;
goto v___jp_474_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_val_481_);
lean_dec(v_key_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_x_459_);
lean_ctor_set(v___x_483_, 0, v_x_458_);
v___x_489_ = v___x_483_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_x_458_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_x_459_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v___y_475_ = v___x_489_;
goto v___jp_474_;
}
}
}
}
case 1:
{
lean_object* v_node_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_502_; 
v_node_492_ = lean_ctor_get(v_v_471_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_v_471_);
if (v_isSharedCheck_502_ == 0)
{
v___x_494_ = v_v_471_;
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_node_492_);
lean_dec(v_v_471_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_496_ = lean_usize_shift_right(v_x_456_, v___x_461_);
v___x_497_ = lean_usize_add(v_x_457_, v___x_462_);
v___x_498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_492_, v___x_496_, v___x_497_, v_x_458_, v_x_459_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_498_);
v___x_500_ = v___x_494_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
v___y_475_ = v___x_500_;
goto v___jp_474_;
}
}
}
default: 
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_x_458_);
lean_ctor_set(v___x_503_, 1, v_x_459_);
v___y_475_ = v___x_503_;
goto v___jp_474_;
}
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_array_fset(v_xs_x27_473_, v_j_465_, v___y_475_);
lean_dec(v_j_465_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_476_);
v___x_478_ = v___x_469_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_ks_506_; lean_object* v_vs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_527_; 
v_ks_506_ = lean_ctor_get(v_x_455_, 0);
v_vs_507_ = lean_ctor_get(v_x_455_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_527_ == 0)
{
v___x_509_ = v_x_455_;
v_isShared_510_ = v_isSharedCheck_527_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_vs_507_);
lean_inc(v_ks_506_);
lean_dec(v_x_455_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_527_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_ks_506_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_vs_507_);
v___x_512_ = v_reuseFailAlloc_526_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v_newNode_513_; uint8_t v___y_515_; size_t v___x_521_; uint8_t v___x_522_; 
v_newNode_513_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v___x_512_, v_x_458_, v_x_459_);
v___x_521_ = ((size_t)7ULL);
v___x_522_ = lean_usize_dec_le(v___x_521_, v_x_457_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_513_);
v___x_524_ = lean_unsigned_to_nat(4u);
v___x_525_ = lean_nat_dec_lt(v___x_523_, v___x_524_);
lean_dec(v___x_523_);
v___y_515_ = v___x_525_;
goto v___jp_514_;
}
else
{
v___y_515_ = v___x_522_;
goto v___jp_514_;
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_object* v_ks_516_; lean_object* v_vs_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_ks_516_ = lean_ctor_get(v_newNode_513_, 0);
lean_inc_ref(v_ks_516_);
v_vs_517_ = lean_ctor_get(v_newNode_513_, 1);
lean_inc_ref(v_vs_517_);
lean_dec_ref(v_newNode_513_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2);
v___x_520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_x_457_, v_ks_516_, v_vs_517_, v___x_518_, v___x_519_);
lean_dec_ref(v_vs_517_);
lean_dec_ref(v_ks_516_);
return v___x_520_;
}
else
{
return v_newNode_513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(size_t v_depth_528_, lean_object* v_keys_529_, lean_object* v_vals_530_, lean_object* v_i_531_, lean_object* v_entries_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_get_size(v_keys_529_);
v___x_534_ = lean_nat_dec_lt(v_i_531_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v_i_531_);
return v_entries_532_;
}
else
{
lean_object* v_k_535_; lean_object* v_v_536_; uint64_t v___x_537_; size_t v_h_538_; size_t v___x_539_; lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v_h_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_k_535_ = lean_array_fget_borrowed(v_keys_529_, v_i_531_);
v_v_536_ = lean_array_fget_borrowed(v_vals_530_, v_i_531_);
v___x_537_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_535_);
v_h_538_ = lean_uint64_to_usize(v___x_537_);
v___x_539_ = ((size_t)5ULL);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_sub(v_depth_528_, v___x_541_);
v___x_543_ = lean_usize_mul(v___x_539_, v___x_542_);
v_h_544_ = lean_usize_shift_right(v_h_538_, v___x_543_);
v___x_545_ = lean_nat_add(v_i_531_, v___x_540_);
lean_dec(v_i_531_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
v___x_546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_532_, v_h_544_, v_depth_528_, v_k_535_, v_v_536_);
v_i_531_ = v___x_545_;
v_entries_532_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg___boxed(lean_object* v_depth_548_, lean_object* v_keys_549_, lean_object* v_vals_550_, lean_object* v_i_551_, lean_object* v_entries_552_){
_start:
{
size_t v_depth_boxed_553_; lean_object* v_res_554_; 
v_depth_boxed_553_ = lean_unbox_usize(v_depth_548_);
lean_dec(v_depth_548_);
v_res_554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_boxed_553_, v_keys_549_, v_vals_550_, v_i_551_, v_entries_552_);
lean_dec_ref(v_vals_550_);
lean_dec_ref(v_keys_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
size_t v_x_21156__boxed_560_; size_t v_x_21157__boxed_561_; lean_object* v_res_562_; 
v_x_21156__boxed_560_ = lean_unbox_usize(v_x_556_);
lean_dec(v_x_556_);
v_x_21157__boxed_561_ = lean_unbox_usize(v_x_557_);
lean_dec(v_x_557_);
v_res_562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_555_, v_x_21156__boxed_560_, v_x_21157__boxed_561_, v_x_558_, v_x_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint64_t v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_566_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_564_);
v___x_567_ = lean_uint64_to_usize(v___x_566_);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_563_, v___x_567_, v___x_568_, v_x_564_, v_x_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object* v___x_570_, lean_object* v_a_571_, lean_object* v_s_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_s_572_, v___x_570_, v_a_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_h_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v___x_583_ = lean_array_push(v___x_574_, v_h_577_);
v___x_584_ = l_Lean_mkAppN(v___x_575_, v___x_576_);
v___x_585_ = 0;
v___x_586_ = 1;
v___x_587_ = 1;
v___x_588_ = l_Lean_Meta_mkForallFVars(v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_586_, v___x_587_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v___x_583_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v_h_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_589_, v___x_590_, v___x_591_, v_h_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___x_591_);
return v_res_598_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_instMonadEIO(lean_box(0));
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_toApplicative_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_673_; 
v___x_610_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
v___x_611_ = l_StateRefT_x27_instMonad___redArg(v___x_610_);
v_toApplicative_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_611_, 1);
lean_dec(v_unused_674_);
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_673_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_toApplicative_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_673_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_toFunctor_616_; lean_object* v_toSeq_617_; lean_object* v_toSeqLeft_618_; lean_object* v_toSeqRight_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_671_; 
v_toFunctor_616_ = lean_ctor_get(v_toApplicative_612_, 0);
v_toSeq_617_ = lean_ctor_get(v_toApplicative_612_, 2);
v_toSeqLeft_618_ = lean_ctor_get(v_toApplicative_612_, 3);
v_toSeqRight_619_ = lean_ctor_get(v_toApplicative_612_, 4);
v_isSharedCheck_671_ = !lean_is_exclusive(v_toApplicative_612_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_toApplicative_612_, 1);
lean_dec(v_unused_672_);
v___x_621_ = v_toApplicative_612_;
v_isShared_622_ = v_isSharedCheck_671_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_toSeqRight_619_);
lean_inc(v_toSeqLeft_618_);
lean_inc(v_toSeq_617_);
lean_inc(v_toFunctor_616_);
lean_dec(v_toApplicative_612_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_671_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_632_; 
v___f_623_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1));
v___f_624_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_616_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_625_, 0, v_toFunctor_616_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_616_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___f_625_);
lean_ctor_set(v___x_627_, 1, v___f_626_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toSeqRight_619_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqLeft_618_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeq_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___f_628_);
lean_ctor_set(v___x_621_, 3, v___f_629_);
lean_ctor_set(v___x_621_, 2, v___f_630_);
lean_ctor_set(v___x_621_, 1, v___f_623_);
lean_ctor_set(v___x_621_, 0, v___x_627_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v___f_628_);
v___x_632_ = v_reuseFailAlloc_670_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___f_624_);
lean_ctor_set(v___x_614_, 0, v___x_632_);
v___x_634_ = v___x_614_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___f_624_);
v___x_634_ = v_reuseFailAlloc_669_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v_toApplicative_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_667_; 
v___x_635_ = l_StateRefT_x27_instMonad___redArg(v___x_634_);
v_toApplicative_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v___x_635_, 1);
lean_dec(v_unused_668_);
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_667_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_toApplicative_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_667_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_toFunctor_640_; lean_object* v_toSeq_641_; lean_object* v_toSeqLeft_642_; lean_object* v_toSeqRight_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_665_; 
v_toFunctor_640_ = lean_ctor_get(v_toApplicative_636_, 0);
v_toSeq_641_ = lean_ctor_get(v_toApplicative_636_, 2);
v_toSeqLeft_642_ = lean_ctor_get(v_toApplicative_636_, 3);
v_toSeqRight_643_ = lean_ctor_get(v_toApplicative_636_, 4);
v_isSharedCheck_665_ = !lean_is_exclusive(v_toApplicative_636_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_toApplicative_636_, 1);
lean_dec(v_unused_666_);
v___x_645_ = v_toApplicative_636_;
v_isShared_646_ = v_isSharedCheck_665_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_toSeqRight_643_);
lean_inc(v_toSeqLeft_642_);
lean_inc(v_toSeq_641_);
lean_inc(v_toFunctor_640_);
lean_dec(v_toApplicative_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_665_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___x_656_; 
v___f_647_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3));
v___f_648_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_640_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_649_, 0, v_toFunctor_640_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_650_, 0, v_toFunctor_640_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___f_649_);
lean_ctor_set(v___x_651_, 1, v___f_650_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_652_, 0, v_toSeqRight_643_);
v___f_653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_653_, 0, v_toSeqLeft_642_);
v___f_654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_654_, 0, v_toSeq_641_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v___f_652_);
lean_ctor_set(v___x_645_, 3, v___f_653_);
lean_ctor_set(v___x_645_, 2, v___f_654_);
lean_ctor_set(v___x_645_, 1, v___f_647_);
lean_ctor_set(v___x_645_, 0, v___x_651_);
v___x_656_ = v___x_645_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___f_647_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v___f_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___f_653_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v___f_652_);
v___x_656_ = v_reuseFailAlloc_664_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___f_648_);
lean_ctor_set(v___x_638_, 0, v___x_656_);
v___x_658_ = v___x_638_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___f_648_);
v___x_658_ = v_reuseFailAlloc_663_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_17258__overap_661_; lean_object* v___x_662_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_instInhabitedOfMonad___redArg(v___x_658_, v___x_659_);
v___x_17258__overap_661_ = lean_panic_fn_borrowed(v___x_660_, v_msg_604_);
lean_dec(v___x_660_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
v___x_662_ = lean_apply_5(v___x_17258__overap_661_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
return v___x_662_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(lean_object* v_msgData_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v___x_690_; lean_object* v_mctx_691_; lean_object* v_lctx_692_; lean_object* v_options_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_689_);
lean_dec(v___x_688_);
v___x_690_ = lean_st_ref_get(v___y_684_);
v_mctx_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_mctx_691_);
lean_dec(v___x_690_);
v_lctx_692_ = lean_ctor_get(v___y_683_, 2);
v_options_693_ = lean_ctor_get(v___y_685_, 2);
lean_inc_ref(v_options_693_);
lean_inc_ref(v_lctx_692_);
v___x_694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_694_, 0, v_env_689_);
lean_ctor_set(v___x_694_, 1, v_mctx_691_);
lean_ctor_set(v___x_694_, 2, v_lctx_692_);
lean_ctor_set(v___x_694_, 3, v_options_693_);
v___x_695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_msgData_682_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(lean_object* v_msgData_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msgData_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_ref_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_ref_710_ = lean_ctor_get(v___y_707_, 5);
v___x_711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_inc(v_ref_710_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_ref_710_);
lean_ctor_set(v___x_716_, 1, v_a_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 1);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2));
v___x_733_ = l_Lean_stringToMessageData(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_737_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_738_ = lean_unsigned_to_nat(11u);
v___x_739_ = lean_unsigned_to_nat(122u);
v___x_740_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_741_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_742_ = l_mkPanicMessageWithDecl(v___x_741_, v___x_740_, v___x_739_, v___x_738_, v___x_737_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_757_; lean_object* v_env_758_; uint8_t v___x_759_; lean_object* v___x_760_; 
v___x_757_ = lean_st_ref_get(v___y_747_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc_ref(v_env_758_);
lean_dec(v___x_757_);
v___x_759_ = 0;
lean_inc(v_constName_743_);
v___x_760_ = l_Lean_Environment_findAsync_x3f(v_env_758_, v_constName_743_, v___x_759_);
if (lean_obj_tag(v___x_760_) == 1)
{
lean_object* v_val_761_; uint8_t v_kind_762_; 
v_val_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref(v___x_760_);
v_kind_762_ = lean_ctor_get_uint8(v_val_761_, sizeof(void*)*3);
if (v_kind_762_ == 6)
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_761_);
if (lean_obj_tag(v___x_763_) == 6)
{
lean_object* v_val_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_constName_743_);
v_val_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_val_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 0);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_val_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v___x_763_);
v___x_772_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7);
v___x_773_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_772_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
if (lean_obj_tag(v_a_774_) == 0)
{
lean_del_object(v___x_776_);
goto v___jp_749_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_780_; 
lean_dec(v_constName_743_);
v_val_778_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_val_778_);
lean_dec_ref(v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_val_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_constName_743_);
v_a_783_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_773_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
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
else
{
lean_dec(v_val_761_);
goto v___jp_749_;
}
}
else
{
lean_dec(v___x_760_);
goto v___jp_749_;
}
v___jp_749_:
{
lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_750_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_751_ = 0;
v___x_752_ = l_Lean_MessageData_ofConstName(v_constName_743_, v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_755_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v___x_798_, size_t v_sz_799_, size_t v_i_800_, lean_object* v_bs_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_bs_801_);
return v___x_808_;
}
else
{
lean_object* v_v_809_; lean_object* v___x_810_; 
v_v_809_ = lean_array_uget_borrowed(v_bs_801_, v_i_800_);
lean_inc(v_v_809_);
v___x_810_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_809_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_cidx_812_; lean_object* v_start_813_; lean_object* v_stop_814_; lean_object* v___x_815_; lean_object* v_bs_x27_816_; lean_object* v_a_818_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___x_810_);
v_cidx_812_ = lean_ctor_get(v_a_811_, 2);
lean_inc(v_cidx_812_);
lean_dec(v_a_811_);
v_start_813_ = lean_ctor_get(v___x_798_, 1);
v_stop_814_ = lean_ctor_get(v___x_798_, 2);
v___x_815_ = lean_unsigned_to_nat(0u);
v_bs_x27_816_ = lean_array_uset(v_bs_801_, v_i_800_, v___x_815_);
v___x_823_ = lean_nat_sub(v_stop_814_, v_start_813_);
v___x_824_ = lean_nat_dec_lt(v_cidx_812_, v___x_823_);
lean_dec(v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_cidx_812_);
v___x_825_ = l_Lean_instInhabitedExpr;
v___x_826_ = l_outOfBounds___redArg(v___x_825_);
v_a_818_ = v___x_826_;
goto v___jp_817_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Subarray_get___redArg(v___x_798_, v_cidx_812_);
lean_dec(v_cidx_812_);
v_a_818_ = v___x_827_;
goto v___jp_817_;
}
v___jp_817_:
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_800_, v___x_819_);
v___x_821_ = lean_array_uset(v_bs_x27_816_, v_i_800_, v_a_818_);
v_i_800_ = v___x_820_;
v_bs_801_ = v___x_821_;
goto _start;
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v_bs_801_);
v_a_828_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_810_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_810_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(lean_object* v___x_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_845_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_846_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_836_, v_sz_boxed_845_, v_i_boxed_846_, v_bs_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___x_836_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(lean_object* v_xs_848_, lean_object* v_v_849_, lean_object* v_i_850_){
_start:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_array_get_size(v_xs_848_);
v___x_852_ = lean_nat_dec_lt(v_i_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_dec(v_i_850_);
v___x_853_ = lean_box(0);
return v___x_853_;
}
else
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_fget_borrowed(v_xs_848_, v_i_850_);
v___x_855_ = lean_name_eq(v___x_854_, v_v_849_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_i_850_, v___x_856_);
lean_dec(v_i_850_);
v_i_850_ = v___x_857_;
goto _start;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_i_850_);
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(lean_object* v_xs_860_, lean_object* v_v_861_, lean_object* v_i_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_860_, v_v_861_, v_i_862_);
lean_dec(v_v_861_);
lean_dec_ref(v_xs_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(lean_object* v_xs_864_, lean_object* v_v_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_864_, v_v_865_, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(lean_object* v_xs_868_, lean_object* v_v_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_868_, v_v_869_);
lean_dec(v_v_869_);
lean_dec_ref(v_xs_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_xs_871_, lean_object* v_v_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_871_, v_v_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_val_875_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_val_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_xs_883_, lean_object* v_v_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_xs_883_, v_v_884_);
lean_dec(v_v_884_);
lean_dec_ref(v_xs_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(lean_object* v_ctors_886_, lean_object* v_a_887_, lean_object* v___x_888_, lean_object* v_a_889_, uint8_t v___x_890_, uint8_t v___x_891_, lean_object* v_a_892_, lean_object* v_ys_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_ctors_886_, v_a_887_);
if (lean_obj_tag(v___x_900_) == 1)
{
lean_object* v_val_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
lean_dec(v_a_887_);
v_val_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_901_);
lean_dec_ref(v___x_900_);
lean_inc_ref(v_ys_893_);
v___x_902_ = lean_array_pop(v_ys_893_);
v___x_903_ = lean_array_get_borrowed(v___x_888_, v_a_889_, v_val_901_);
lean_dec(v_val_901_);
lean_inc(v___x_903_);
v___x_904_ = l_Lean_mkAppN(v___x_903_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_905_ = 1;
v___x_906_ = l_Lean_Meta_mkLambdaFVars(v_ys_893_, v___x_904_, v___x_890_, v___x_891_, v___x_890_, v___x_891_, v___x_905_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec_ref(v_ys_893_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; 
lean_dec(v___x_900_);
v___x_907_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_887_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_cidx_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v_cidx_909_ = lean_ctor_get(v_a_908_, 2);
lean_inc(v_cidx_909_);
lean_dec(v_a_908_);
v___x_910_ = l_Lean_mkRawNatLit(v_cidx_909_);
v___x_911_ = l_mkHasNotBitProof(v___x_910_, v_a_892_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = lean_array_get_size(v_ys_893_);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_sub(v___x_913_, v___x_914_);
v___x_916_ = lean_array_get_borrowed(v___x_888_, v_ys_893_, v___x_915_);
lean_dec(v___x_915_);
lean_inc(v___x_916_);
v___x_917_ = l_Lean_Expr_app___override(v___x_916_, v_a_912_);
v___x_918_ = 1;
v___x_919_ = l_Lean_Meta_mkLambdaFVars(v_ys_893_, v___x_917_, v___x_890_, v___x_891_, v___x_890_, v___x_891_, v___x_918_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec_ref(v_ys_893_);
return v___x_919_;
}
else
{
lean_dec_ref(v_ys_893_);
return v___x_911_;
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v_ys_893_);
v_a_920_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_907_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_907_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(lean_object* v_ctors_928_, lean_object* v_a_929_, lean_object* v___x_930_, lean_object* v_a_931_, lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v_a_934_, lean_object* v_ys_935_, lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v___x_21824__boxed_942_; uint8_t v___x_21825__boxed_943_; lean_object* v_res_944_; 
v___x_21824__boxed_942_ = lean_unbox(v___x_932_);
v___x_21825__boxed_943_ = lean_unbox(v___x_933_);
v_res_944_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(v_ctors_928_, v_a_929_, v___x_930_, v_a_931_, v___x_21824__boxed_942_, v___x_21825__boxed_943_, v_a_934_, v_ys_935_, v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_x_936_);
lean_dec_ref(v_a_934_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v___x_930_);
lean_dec_ref(v_ctors_928_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_ctors_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_as_948_, lean_object* v_bs_949_, lean_object* v_i_950_, lean_object* v_cs_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_as_948_);
v___x_958_ = lean_nat_dec_lt(v_i_950_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec(v_i_950_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec_ref(v_ctors_945_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_cs_951_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_array_get_size(v_bs_949_);
v___x_961_ = lean_nat_dec_lt(v_i_950_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v_i_950_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec_ref(v_ctors_945_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_cs_951_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v_b_969_; lean_object* v___x_970_; 
v___x_963_ = l_Lean_instInhabitedExpr;
v___x_964_ = 0;
v_a_965_ = lean_array_fget_borrowed(v_as_948_, v_i_950_);
v___x_966_ = lean_box(v___x_964_);
v___x_967_ = lean_box(v___x_961_);
lean_inc_ref(v_a_947_);
lean_inc_ref(v_a_946_);
lean_inc(v_a_965_);
lean_inc_ref(v_ctors_945_);
v___f_968_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_968_, 0, v_ctors_945_);
lean_closure_set(v___f_968_, 1, v_a_965_);
lean_closure_set(v___f_968_, 2, v___x_963_);
lean_closure_set(v___f_968_, 3, v_a_946_);
lean_closure_set(v___f_968_, 4, v___x_966_);
lean_closure_set(v___f_968_, 5, v___x_967_);
lean_closure_set(v___f_968_, 6, v_a_947_);
v_b_969_ = lean_array_fget_borrowed(v_bs_949_, v_i_950_);
lean_inc(v_b_969_);
v___x_970_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_b_969_, v___f_968_, v___x_964_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_i_950_, v___x_972_);
lean_dec(v_i_950_);
v___x_974_ = lean_array_push(v_cs_951_, v_a_971_);
v_i_950_ = v___x_973_;
v_cs_951_ = v___x_974_;
goto _start;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_cs_951_);
lean_dec(v_i_950_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec_ref(v_ctors_945_);
v_a_976_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_970_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_ctors_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_as_987_, lean_object* v_bs_988_, lean_object* v_i_989_, lean_object* v_cs_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_984_, v_a_985_, v_a_986_, v_as_987_, v_bs_988_, v_i_989_, v_cs_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_bs_988_);
lean_dec_ref(v_as_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(size_t v_sz_997_, size_t v_i_998_, lean_object* v_bs_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_bs_999_);
return v___x_1006_;
}
else
{
lean_object* v_v_1007_; lean_object* v___x_1008_; 
v_v_1007_ = lean_array_uget_borrowed(v_bs_999_, v_i_998_);
lean_inc(v_v_1007_);
v___x_1008_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1007_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_cidx_1010_; lean_object* v___x_1011_; lean_object* v_bs_x27_1012_; size_t v___x_1013_; size_t v___x_1014_; lean_object* v___x_1015_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v_cidx_1010_ = lean_ctor_get(v_a_1009_, 2);
lean_inc(v_cidx_1010_);
lean_dec(v_a_1009_);
v___x_1011_ = lean_unsigned_to_nat(0u);
v_bs_x27_1012_ = lean_array_uset(v_bs_999_, v_i_998_, v___x_1011_);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_add(v_i_998_, v___x_1013_);
v___x_1015_ = lean_array_uset(v_bs_x27_1012_, v_i_998_, v_cidx_1010_);
v_i_998_ = v___x_1014_;
v_bs_999_ = v___x_1015_;
goto _start;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_bs_999_);
v_a_1017_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1008_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1008_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_bs_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_boxed_1033_, v_i_boxed_1034_, v_bs_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(lean_object* v_k_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___x_1043_ = lean_apply_6(v_k_1036_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, lean_box(0));
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(lean_object* v_k_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(v_k_1044_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(lean_object* v_name_1052_, uint8_t v_bi_1053_, lean_object* v_type_1054_, lean_object* v_k_1055_, uint8_t v_kind_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1062_, 0, v_k_1055_);
v___x_1063_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1052_, v_bi_1053_, v_type_1054_, v___f_1062_, v_kind_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1063_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1063_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(lean_object* v_name_1080_, lean_object* v_bi_1081_, lean_object* v_type_1082_, lean_object* v_k_1083_, lean_object* v_kind_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v_bi_boxed_1090_; uint8_t v_kind_boxed_1091_; lean_object* v_res_1092_; 
v_bi_boxed_1090_ = lean_unbox(v_bi_1081_);
v_kind_boxed_1091_ = lean_unbox(v_kind_1084_);
v_res_1092_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1080_, v_bi_boxed_1090_, v_type_1082_, v_k_1083_, v_kind_boxed_1091_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(lean_object* v_name_1093_, lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = 0;
v___x_1102_ = 0;
v___x_1103_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1093_, v___x_1101_, v_type_1094_, v_k_1095_, v___x_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(lean_object* v_name_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_1104_, v_type_1105_, v_k_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1124_, lean_object* v___x_1125_, lean_object* v_numIndices_1126_, lean_object* v_ctors_1127_, lean_object* v___x_1128_, lean_object* v___x_1129_, lean_object* v_a_1130_, lean_object* v_ctors_1131_, lean_object* v___x_1132_, lean_object* v_xs_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1248_ = lean_array_get_size(v_xs_1133_);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_add(v_numParams_1124_, v___x_1249_);
v___x_1251_ = lean_nat_add(v___x_1250_, v_numIndices_1126_);
lean_dec(v___x_1250_);
v___x_1252_ = lean_nat_add(v___x_1251_, v___x_1249_);
lean_dec(v___x_1251_);
v___x_1253_ = l_List_lengthTR___redArg(v_ctors_1131_);
v___x_1254_ = lean_nat_add(v___x_1252_, v___x_1253_);
lean_dec(v___x_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_nat_dec_eq(v___x_1248_, v___x_1254_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_xs_1133_);
lean_dec(v_ctors_1131_);
lean_dec(v___x_1129_);
lean_dec(v___x_1128_);
lean_dec_ref(v_ctors_1127_);
lean_dec(v_numParams_1124_);
v___x_1256_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1257_ = l_Lean_MessageData_ofConstName(v___x_1132_, v___x_1255_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1260_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
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
lean_dec(v___x_1132_);
v___y_1141_ = v___y_1135_;
v___y_1142_ = v___y_1136_;
v___y_1143_ = v___y_1137_;
v___y_1144_ = v___y_1138_;
goto v___jp_1140_;
}
v___jp_1140_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1124_);
lean_inc_ref_n(v_xs_1133_, 2);
v___x_1146_ = l_Array_toSubarray___redArg(v_xs_1133_, v___x_1145_, v_numParams_1124_);
v___x_1147_ = lean_array_get(v___x_1125_, v_xs_1133_, v_numParams_1124_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_numParams_1124_, v___x_1148_);
lean_dec(v_numParams_1124_);
v___x_1150_ = lean_nat_add(v___x_1149_, v_numIndices_1126_);
lean_inc(v___x_1150_);
v___x_1151_ = l_Array_toSubarray___redArg(v_xs_1133_, v___x_1149_, v___x_1150_);
v___x_1152_ = lean_array_get(v___x_1125_, v_xs_1133_, v___x_1150_);
v___x_1153_ = lean_nat_add(v___x_1150_, v___x_1148_);
lean_dec(v___x_1150_);
v___x_1154_ = lean_array_get_size(v_xs_1133_);
v___x_1155_ = l_Array_toSubarray___redArg(v_xs_1133_, v___x_1153_, v___x_1154_);
v_sz_1156_ = lean_array_size(v_ctors_1127_);
v___x_1157_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1127_);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_1155_, v_sz_1156_, v___x_1157_, v_ctors_1127_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___x_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v___x_1158_);
lean_inc_ref(v_ctors_1127_);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_1156_, v___x_1157_, v_ctors_1127_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = l_Subarray_copy___redArg(v___x_1151_);
v___x_1163_ = lean_mk_empty_array_with_capacity(v___x_1148_);
lean_inc(v___x_1152_);
lean_inc_ref_n(v___x_1163_, 2);
v___x_1164_ = lean_array_push(v___x_1163_, v___x_1152_);
lean_inc_ref(v___x_1162_);
v___x_1165_ = l_Array_append___redArg(v___x_1162_, v___x_1164_);
lean_inc_ref(v___x_1165_);
lean_inc(v___x_1147_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1166_, 0, v___x_1163_);
lean_closure_set(v___f_1166_, 1, v___x_1147_);
lean_closure_set(v___f_1166_, 2, v___x_1165_);
v___x_1167_ = l_Lean_mkConst(v___x_1128_, v___x_1129_);
v___x_1168_ = l_Subarray_copy___redArg(v___x_1146_);
lean_inc_ref(v___x_1168_);
v___x_1169_ = l_Array_append___redArg(v___x_1168_, v___x_1162_);
v___x_1170_ = l_Array_append___redArg(v___x_1169_, v___x_1164_);
v___x_1171_ = l_Lean_mkAppN(v___x_1167_, v___x_1170_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = l_mkHasNotBit(v___x_1171_, v_a_1161_);
v___x_1173_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1174_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v___x_1173_, v___x_1172_, v___f_1166_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1177_ = l_Lean_Core_mkFreshUserName(v___x_1176_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = 0;
v___x_1180_ = l_Lean_ConstantInfo_value_x21(v_a_1130_, v___x_1179_);
v___x_1181_ = 0;
lean_inc(v___x_1147_);
v___x_1182_ = l_Lean_mkAppN(v___x_1147_, v___x_1165_);
v___x_1183_ = l_Lean_mkForall(v_a_1178_, v___x_1181_, v_a_1175_, v___x_1182_);
v___x_1184_ = 1;
v___x_1185_ = 1;
v___x_1186_ = l_Lean_Meta_mkLambdaFVars(v___x_1165_, v___x_1183_, v___x_1179_, v___x_1184_, v___x_1179_, v___x_1184_, v___x_1185_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___x_1165_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = l_Lean_mkAppN(v___x_1180_, v___x_1168_);
v___x_1189_ = l_Lean_Expr_app___override(v___x_1188_, v_a_1187_);
v___x_1190_ = l_Lean_mkAppN(v___x_1189_, v___x_1162_);
v___x_1191_ = l_Lean_Expr_app___override(v___x_1190_, v___x_1152_);
v___x_1192_ = l_List_lengthTR___redArg(v_ctors_1131_);
lean_inc_ref(v___x_1191_);
v___x_1193_ = l_Lean_Meta_inferArgumentTypesN(v___x_1192_, v___x_1191_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = lean_array_mk(v_ctors_1131_);
v___x_1196_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1159_);
v___x_1197_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_1127_, v_a_1159_, v_a_1161_, v___x_1195_, v_a_1194_, v___x_1145_, v___x_1196_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v_a_1194_);
lean_dec_ref(v___x_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = l_Lean_mkAppN(v___x_1191_, v_a_1198_);
lean_dec(v_a_1198_);
v___x_1200_ = l_Lean_Core_betaReduce(v___x_1199_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_array_push(v___x_1163_, v___x_1147_);
v___x_1203_ = l_Array_append___redArg(v___x_1168_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Array_append___redArg(v___x_1203_, v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1205_ = l_Array_append___redArg(v___x_1204_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1206_ = l_Array_append___redArg(v___x_1205_, v_a_1159_);
lean_dec(v_a_1159_);
v___x_1207_ = l_Lean_Meta_mkLambdaFVars(v___x_1206_, v_a_1201_, v___x_1179_, v___x_1184_, v___x_1179_, v___x_1184_, v___x_1185_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___x_1206_);
return v___x_1207_;
}
else
{
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1159_);
lean_dec(v___x_1147_);
return v___x_1200_;
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1159_);
lean_dec(v___x_1147_);
v_a_1208_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1197_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1197_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1161_);
lean_dec(v_a_1159_);
lean_dec(v___x_1147_);
lean_dec(v_ctors_1131_);
lean_dec_ref(v_ctors_1127_);
v_a_1216_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1193_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1193_);
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
else
{
lean_dec_ref(v___x_1180_);
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1161_);
lean_dec(v_a_1159_);
lean_dec(v___x_1152_);
lean_dec(v___x_1147_);
lean_dec(v_ctors_1131_);
lean_dec_ref(v_ctors_1127_);
return v___x_1186_;
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1175_);
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1161_);
lean_dec(v_a_1159_);
lean_dec(v___x_1152_);
lean_dec(v___x_1147_);
lean_dec(v_ctors_1131_);
lean_dec_ref(v_ctors_1127_);
v_a_1224_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1177_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1177_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_dec_ref(v___x_1168_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___x_1162_);
lean_dec(v_a_1161_);
lean_dec(v_a_1159_);
lean_dec(v___x_1152_);
lean_dec(v___x_1147_);
lean_dec(v_ctors_1131_);
lean_dec_ref(v_ctors_1127_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1159_);
lean_dec(v___x_1152_);
lean_dec_ref(v___x_1151_);
lean_dec(v___x_1147_);
lean_dec_ref(v___x_1146_);
lean_dec(v_ctors_1131_);
lean_dec(v___x_1129_);
lean_dec(v___x_1128_);
lean_dec_ref(v_ctors_1127_);
v_a_1232_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1160_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1160_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v___x_1152_);
lean_dec_ref(v___x_1151_);
lean_dec(v___x_1147_);
lean_dec_ref(v___x_1146_);
lean_dec(v_ctors_1131_);
lean_dec(v___x_1129_);
lean_dec(v___x_1128_);
lean_dec_ref(v_ctors_1127_);
v_a_1240_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1158_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1158_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object* v_numParams_1270_, lean_object* v___x_1271_, lean_object* v_numIndices_1272_, lean_object* v_ctors_1273_, lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v_a_1276_, lean_object* v_ctors_1277_, lean_object* v___x_1278_, lean_object* v_xs_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1270_, v___x_1271_, v_numIndices_1272_, v_ctors_1273_, v___x_1274_, v___x_1275_, v_a_1276_, v_ctors_1277_, v___x_1278_, v_xs_1279_, v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_x_1280_);
lean_dec_ref(v_a_1276_);
lean_dec(v_numIndices_1272_);
lean_dec_ref(v___x_1271_);
return v_res_1286_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_a_1287_, lean_object* v_x_1288_){
_start:
{
if (lean_obj_tag(v_x_1288_) == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 0;
return v___x_1289_;
}
else
{
lean_object* v_head_1290_; lean_object* v_tail_1291_; uint8_t v___x_1292_; 
v_head_1290_ = lean_ctor_get(v_x_1288_, 0);
v_tail_1291_ = lean_ctor_get(v_x_1288_, 1);
v___x_1292_ = lean_name_eq(v_a_1287_, v_head_1290_);
if (v___x_1292_ == 0)
{
v_x_1288_ = v_tail_1291_;
goto _start;
}
else
{
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec(v_a_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1304_, lean_object* v_indName_1305_, lean_object* v_as_1306_, size_t v_sz_1307_, size_t v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_a_1316_; uint8_t v___x_1320_; 
v___x_1320_ = lean_usize_dec_lt(v_i_1308_, v_sz_1307_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_indName_1305_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_b_1309_);
return v___x_1321_;
}
else
{
lean_object* v_ctors_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; uint8_t v___x_1325_; 
v_ctors_1322_ = lean_ctor_get(v_a_1304_, 4);
v___x_1323_ = lean_box(0);
v_a_1324_ = lean_array_uget_borrowed(v_as_1306_, v_i_1308_);
v___x_1325_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1324_, v_ctors_1322_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1326_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1);
lean_inc(v_a_1324_);
v___x_1327_ = l_Lean_MessageData_ofName(v_a_1324_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_inc(v_indName_1305_);
v___x_1331_ = l_Lean_MessageData_ofName(v_indName_1305_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1332_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref(v___x_1333_);
v_a_1316_ = v___x_1323_;
goto v___jp_1315_;
}
else
{
lean_dec(v_indName_1305_);
return v___x_1333_;
}
}
else
{
v_a_1316_ = v___x_1323_;
goto v___jp_1315_;
}
}
v___jp_1315_:
{
size_t v___x_1317_; size_t v___x_1318_; 
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_add(v_i_1308_, v___x_1317_);
v_i_1308_ = v___x_1318_;
v_b_1309_ = v_a_1316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1334_, lean_object* v_indName_1335_, lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1334_, v_indName_1335_, v_as_1336_, v_sz_boxed_1345_, v_i_boxed_1346_, v_b_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_as_1336_);
lean_dec_ref(v_a_1334_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
if (lean_obj_tag(v_a_1348_) == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = l_List_reverse___redArg(v_a_1349_);
return v___x_1350_;
}
else
{
lean_object* v_head_1351_; lean_object* v_tail_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1361_; 
v_head_1351_ = lean_ctor_get(v_a_1348_, 0);
v_tail_1352_ = lean_ctor_get(v_a_1348_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_a_1348_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1354_ = v_a_1348_;
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_tail_1352_);
lean_inc(v_head_1351_);
lean_dec(v_a_1348_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_Lean_mkLevelParam(v_head_1351_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_a_1349_);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_a_1349_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v_a_1348_ = v_tail_1352_;
v_a_1349_ = v___x_1358_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1368_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
lean_ctor_set(v___x_1368_, 3, v___x_1367_);
lean_ctor_set(v___x_1368_, 4, v___x_1367_);
lean_ctor_set(v___x_1368_, 5, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(lean_object* v_declName_1369_, uint8_t v_s_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_env_1375_; lean_object* v_nextMacroScope_1376_; lean_object* v_ngen_1377_; lean_object* v_auxDeclNGen_1378_; lean_object* v_traceState_1379_; lean_object* v_messages_1380_; lean_object* v_infoState_1381_; lean_object* v_snapshotTasks_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1411_; 
v___x_1374_ = lean_st_ref_take(v___y_1372_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
v_nextMacroScope_1376_ = lean_ctor_get(v___x_1374_, 1);
v_ngen_1377_ = lean_ctor_get(v___x_1374_, 2);
v_auxDeclNGen_1378_ = lean_ctor_get(v___x_1374_, 3);
v_traceState_1379_ = lean_ctor_get(v___x_1374_, 4);
v_messages_1380_ = lean_ctor_get(v___x_1374_, 6);
v_infoState_1381_ = lean_ctor_get(v___x_1374_, 7);
v_snapshotTasks_1382_ = lean_ctor_get(v___x_1374_, 8);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1374_, 5);
lean_dec(v_unused_1412_);
v___x_1384_ = v___x_1374_;
v_isShared_1385_ = v_isSharedCheck_1411_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_snapshotTasks_1382_);
lean_inc(v_infoState_1381_);
lean_inc(v_messages_1380_);
lean_inc(v_traceState_1379_);
lean_inc(v_auxDeclNGen_1378_);
lean_inc(v_ngen_1377_);
lean_inc(v_nextMacroScope_1376_);
lean_inc(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1411_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1386_ = 0;
v___x_1387_ = lean_box(0);
v___x_1388_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1375_, v_declName_1369_, v_s_1370_, v___x_1386_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 5, v___x_1389_);
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1391_ = v___x_1384_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_nextMacroScope_1376_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_ngen_1377_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_auxDeclNGen_1378_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_traceState_1379_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1410_, 6, v_messages_1380_);
lean_ctor_set(v_reuseFailAlloc_1410_, 7, v_infoState_1381_);
lean_ctor_set(v_reuseFailAlloc_1410_, 8, v_snapshotTasks_1382_);
v___x_1391_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_mctx_1394_; lean_object* v_zetaDeltaFVarIds_1395_; lean_object* v_postponed_1396_; lean_object* v_diag_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v___x_1392_ = lean_st_ref_set(v___y_1372_, v___x_1391_);
v___x_1393_ = lean_st_ref_take(v___y_1371_);
v_mctx_1394_ = lean_ctor_get(v___x_1393_, 0);
v_zetaDeltaFVarIds_1395_ = lean_ctor_get(v___x_1393_, 2);
v_postponed_1396_ = lean_ctor_get(v___x_1393_, 3);
v_diag_1397_ = lean_ctor_get(v___x_1393_, 4);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v___x_1393_, 1);
lean_dec(v_unused_1409_);
v___x_1399_ = v___x_1393_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_diag_1397_);
lean_inc(v_postponed_1396_);
lean_inc(v_zetaDeltaFVarIds_1395_);
lean_inc(v_mctx_1394_);
lean_dec(v___x_1393_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_mctx_1394_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_zetaDeltaFVarIds_1395_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_postponed_1396_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_diag_1397_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_st_ref_set(v___y_1371_, v___x_1403_);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(lean_object* v_declName_1413_, lean_object* v_s_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_s_boxed_1418_; lean_object* v_res_1419_; 
v_s_boxed_1418_ = lean_unbox(v_s_1414_);
v_res_1419_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1413_, v_s_boxed_1418_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec(v___y_1415_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_declName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = 0;
v___x_1427_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1420_, v___x_1426_, v___y_1422_, v___y_1424_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_declName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_declName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_constName_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_env_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_st_ref_get(v___y_1442_);
v_env_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc_ref(v_env_1445_);
lean_dec(v___x_1444_);
lean_inc(v_constName_1438_);
v___x_1446_ = l_Lean_isInductiveCore_x3f(v_env_1445_, v_constName_1438_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1447_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1448_ = 0;
v___x_1449_ = l_Lean_MessageData_ofConstName(v_constName_1438_, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1447_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1452_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1453_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_constName_1438_);
v_val_1454_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1446_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_val_1454_);
lean_dec(v___x_1446_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 0);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_val_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_constName_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_constName_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(lean_object* v_ref_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_fileName_1476_; lean_object* v_fileMap_1477_; lean_object* v_options_1478_; lean_object* v_currRecDepth_1479_; lean_object* v_maxRecDepth_1480_; lean_object* v_ref_1481_; lean_object* v_currNamespace_1482_; lean_object* v_openDecls_1483_; lean_object* v_initHeartbeats_1484_; lean_object* v_maxHeartbeats_1485_; lean_object* v_quotContext_1486_; lean_object* v_currMacroScope_1487_; uint8_t v_diag_1488_; lean_object* v_cancelTk_x3f_1489_; uint8_t v_suppressElabErrors_1490_; lean_object* v_inheritedTraceOptions_1491_; lean_object* v_ref_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_fileName_1476_ = lean_ctor_get(v___y_1473_, 0);
v_fileMap_1477_ = lean_ctor_get(v___y_1473_, 1);
v_options_1478_ = lean_ctor_get(v___y_1473_, 2);
v_currRecDepth_1479_ = lean_ctor_get(v___y_1473_, 3);
v_maxRecDepth_1480_ = lean_ctor_get(v___y_1473_, 4);
v_ref_1481_ = lean_ctor_get(v___y_1473_, 5);
v_currNamespace_1482_ = lean_ctor_get(v___y_1473_, 6);
v_openDecls_1483_ = lean_ctor_get(v___y_1473_, 7);
v_initHeartbeats_1484_ = lean_ctor_get(v___y_1473_, 8);
v_maxHeartbeats_1485_ = lean_ctor_get(v___y_1473_, 9);
v_quotContext_1486_ = lean_ctor_get(v___y_1473_, 10);
v_currMacroScope_1487_ = lean_ctor_get(v___y_1473_, 11);
v_diag_1488_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*14);
v_cancelTk_x3f_1489_ = lean_ctor_get(v___y_1473_, 12);
v_suppressElabErrors_1490_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1491_ = lean_ctor_get(v___y_1473_, 13);
v_ref_1492_ = l_Lean_replaceRef(v_ref_1469_, v_ref_1481_);
lean_inc_ref(v_inheritedTraceOptions_1491_);
lean_inc(v_cancelTk_x3f_1489_);
lean_inc(v_currMacroScope_1487_);
lean_inc(v_quotContext_1486_);
lean_inc(v_maxHeartbeats_1485_);
lean_inc(v_initHeartbeats_1484_);
lean_inc(v_openDecls_1483_);
lean_inc(v_currNamespace_1482_);
lean_inc(v_maxRecDepth_1480_);
lean_inc(v_currRecDepth_1479_);
lean_inc_ref(v_options_1478_);
lean_inc_ref(v_fileMap_1477_);
lean_inc_ref(v_fileName_1476_);
v___x_1493_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1493_, 0, v_fileName_1476_);
lean_ctor_set(v___x_1493_, 1, v_fileMap_1477_);
lean_ctor_set(v___x_1493_, 2, v_options_1478_);
lean_ctor_set(v___x_1493_, 3, v_currRecDepth_1479_);
lean_ctor_set(v___x_1493_, 4, v_maxRecDepth_1480_);
lean_ctor_set(v___x_1493_, 5, v_ref_1492_);
lean_ctor_set(v___x_1493_, 6, v_currNamespace_1482_);
lean_ctor_set(v___x_1493_, 7, v_openDecls_1483_);
lean_ctor_set(v___x_1493_, 8, v_initHeartbeats_1484_);
lean_ctor_set(v___x_1493_, 9, v_maxHeartbeats_1485_);
lean_ctor_set(v___x_1493_, 10, v_quotContext_1486_);
lean_ctor_set(v___x_1493_, 11, v_currMacroScope_1487_);
lean_ctor_set(v___x_1493_, 12, v_cancelTk_x3f_1489_);
lean_ctor_set(v___x_1493_, 13, v_inheritedTraceOptions_1491_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14, v_diag_1488_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14 + 1, v_suppressElabErrors_1490_);
v___x_1494_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_1470_, v___y_1471_, v___y_1472_, v___x_1493_, v___y_1474_);
lean_dec_ref(v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object* v_ref_1495_, lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1495_, v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_ref_1495_);
return v_res_1502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0(void){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set(v___x_1508_, 3, v___x_1507_);
lean_ctor_set(v___x_1508_, 4, v___x_1506_);
lean_ctor_set(v___x_1508_, 5, v___x_1506_);
lean_ctor_set(v___x_1508_, 6, v___x_1506_);
lean_ctor_set(v___x_1508_, 7, v___x_1506_);
lean_ctor_set(v___x_1508_, 8, v___x_1506_);
lean_ctor_set(v___x_1508_, 9, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(32u);
v___x_1510_ = lean_mk_empty_array_with_capacity(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4(void){
_start:
{
size_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1512_ = ((size_t)5ULL);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_unsigned_to_nat(32u);
v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1514_);
v___x_1516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3);
v___x_1517_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
lean_ctor_set(v___x_1517_, 2, v___x_1513_);
lean_ctor_set(v___x_1517_, 3, v___x_1513_);
lean_ctor_set_usize(v___x_1517_, 4, v___x_1512_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_box(1);
v___x_1519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4);
v___x_1520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object* v_msg_1543_, lean_object* v_declHint_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v_env_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_st_ref_get(v___y_1545_);
v_env_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc_ref(v_env_1548_);
lean_dec(v___x_1547_);
v___x_1549_ = l_Lean_Name_isAnonymous(v_declHint_1544_);
if (v___x_1549_ == 0)
{
uint8_t v_isExporting_1550_; 
v_isExporting_1550_ = lean_ctor_get_uint8(v_env_1548_, sizeof(void*)*8);
if (v_isExporting_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_msg_1543_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
lean_inc_ref(v_env_1548_);
v___x_1552_ = l_Lean_Environment_setExporting(v_env_1548_, v___x_1549_);
lean_inc(v_declHint_1544_);
lean_inc_ref(v___x_1552_);
v___x_1553_ = l_Lean_Environment_contains(v___x_1552_, v_declHint_1544_, v_isExporting_1550_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_msg_1543_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_c_1560_; lean_object* v___x_1561_; 
v___x_1555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2);
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5);
v___x_1557_ = l_Lean_Options_empty;
v___x_1558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1552_);
lean_ctor_set(v___x_1558_, 1, v___x_1555_);
lean_ctor_set(v___x_1558_, 2, v___x_1556_);
lean_ctor_set(v___x_1558_, 3, v___x_1557_);
lean_inc(v_declHint_1544_);
v___x_1559_ = l_Lean_MessageData_ofConstName(v_declHint_1544_, v___x_1549_);
v_c_1560_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1560_, 0, v___x_1558_);
lean_ctor_set(v_c_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1548_, v_declHint_1544_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_c_1560_);
v___x_1564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_MessageData_note(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_msg_1543_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1604_; 
v_val_1569_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1571_ = v___x_1561_;
v_isShared_1572_ = v_isSharedCheck_1604_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_val_1569_);
lean_dec(v___x_1561_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1604_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_mod_1576_; uint8_t v___x_1577_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Lean_Environment_header(v_env_1548_);
lean_dec_ref(v_env_1548_);
v___x_1575_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1574_);
v_mod_1576_ = lean_array_get(v___x_1573_, v___x_1575_, v_val_1569_);
lean_dec(v_val_1569_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = l_Lean_isPrivateName(v_declHint_1544_);
lean_dec(v_declHint_1544_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_c_1560_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_MessageData_ofName(v_mod_1576_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_MessageData_note(v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_msg_1543_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1587_);
v___x_1589_ = v___x_1571_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_c_1560_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_MessageData_ofName(v_mod_1576_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = l_Lean_MessageData_note(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_msg_1543_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1600_);
v___x_1602_ = v___x_1571_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
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
}
}
}
else
{
lean_object* v___x_1605_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1543_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object* v_msg_1606_, lean_object* v_declHint_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1606_, v_declHint_1607_, v___y_1608_);
lean_dec(v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object* v_msg_1611_, lean_object* v_declHint_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
v___x_1618_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1611_, v_declHint_1612_, v___y_1616_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1623_ = l_Lean_unknownIdentifierMessageTag;
v___x_1624_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1624_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object* v_msg_1629_, lean_object* v_declHint_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1629_, v_declHint_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object* v_ref_1637_, lean_object* v_msg_1638_, lean_object* v_declHint_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1647_; 
v___x_1645_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1638_, v_declHint_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1637_, v_a_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object* v_ref_1648_, lean_object* v_msg_1649_, lean_object* v_declHint_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1648_, v_msg_1649_, v_declHint_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_ref_1648_);
return v_res_1656_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object* v_ref_1660_, lean_object* v_constName_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1667_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1);
v___x_1668_ = 0;
lean_inc(v_constName_1661_);
v___x_1669_ = l_Lean_MessageData_ofConstName(v_constName_1661_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1667_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1660_, v___x_1672_, v_constName_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object* v_ref_1674_, lean_object* v_constName_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1674_, v_constName_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v_ref_1674_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_ref_1688_; lean_object* v___x_1689_; 
v_ref_1688_ = lean_ctor_get(v___y_1685_, 5);
v___x_1689_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1688_, v_constName_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object* v_constName_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_env_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = lean_st_ref_get(v___y_1701_);
v_env_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_env_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = 0;
lean_inc(v_constName_1697_);
v___x_1706_ = l_Lean_Environment_find_x3f(v_env_1704_, v_constName_1697_, v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1707_;
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_constName_1697_);
v_val_1708_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1706_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_val_1708_);
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 0);
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_val_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_1723_, lean_object* v_vals_1724_, lean_object* v_i_1725_, lean_object* v_k_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_array_get_size(v_keys_1723_);
v___x_1728_ = lean_nat_dec_lt(v_i_1725_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec(v_i_1725_);
v___x_1729_ = lean_box(0);
return v___x_1729_;
}
else
{
lean_object* v_k_x27_1730_; uint8_t v___x_1731_; 
v_k_x27_1730_ = lean_array_fget_borrowed(v_keys_1723_, v_i_1725_);
v___x_1731_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_1726_, v_k_x27_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_i_1725_, v___x_1732_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1733_;
goto _start;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_array_fget_borrowed(v_vals_1724_, v_i_1725_);
lean_dec(v_i_1725_);
lean_inc(v___x_1735_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_1737_, lean_object* v_vals_1738_, lean_object* v_i_1739_, lean_object* v_k_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_1737_, v_vals_1738_, v_i_1739_, v_k_1740_);
lean_dec_ref(v_k_1740_);
lean_dec_ref(v_vals_1738_);
lean_dec_ref(v_keys_1737_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_1742_, size_t v_x_1743_, lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 0)
{
lean_object* v_es_1745_; lean_object* v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; lean_object* v_j_1750_; lean_object* v___x_1751_; 
v_es_1745_ = lean_ctor_get(v_x_1742_, 0);
v___x_1746_ = lean_box(2);
v___x_1747_ = ((size_t)5ULL);
v___x_1748_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1);
v___x_1749_ = lean_usize_land(v_x_1743_, v___x_1748_);
v_j_1750_ = lean_usize_to_nat(v___x_1749_);
v___x_1751_ = lean_array_get_borrowed(v___x_1746_, v_es_1745_, v_j_1750_);
lean_dec(v_j_1750_);
switch(lean_obj_tag(v___x_1751_))
{
case 0:
{
lean_object* v_key_1752_; lean_object* v_val_1753_; uint8_t v___x_1754_; 
v_key_1752_ = lean_ctor_get(v___x_1751_, 0);
v_val_1753_ = lean_ctor_get(v___x_1751_, 1);
v___x_1754_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_1744_, v_key_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
lean_inc(v_val_1753_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_val_1753_);
return v___x_1756_;
}
}
case 1:
{
lean_object* v_node_1757_; size_t v___x_1758_; 
v_node_1757_ = lean_ctor_get(v___x_1751_, 0);
v___x_1758_ = lean_usize_shift_right(v_x_1743_, v___x_1747_);
v_x_1742_ = v_node_1757_;
v_x_1743_ = v___x_1758_;
goto _start;
}
default: 
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_box(0);
return v___x_1760_;
}
}
}
else
{
lean_object* v_ks_1761_; lean_object* v_vs_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_ks_1761_ = lean_ctor_get(v_x_1742_, 0);
v_vs_1762_ = lean_ctor_get(v_x_1742_, 1);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_ks_1761_, v_vs_1762_, v___x_1763_, v_x_1744_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
size_t v_x_23197__boxed_1768_; lean_object* v_res_1769_; 
v_x_23197__boxed_1768_ = lean_unbox_usize(v_x_1766_);
lean_dec(v_x_1766_);
v_res_1769_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1765_, v_x_23197__boxed_1768_, v_x_1767_);
lean_dec_ref(v_x_1767_);
lean_dec_ref(v_x_1765_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
uint64_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_1771_);
v___x_1773_ = lean_uint64_to_usize(v___x_1772_);
v___x_1774_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1770_, v___x_1773_, v_x_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_1775_, v_x_1776_);
lean_dec_ref(v_x_1776_);
lean_dec_ref(v_x_1775_);
return v_res_1777_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1780_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_1781_ = lean_unsigned_to_nat(42u);
v___x_1782_ = lean_unsigned_to_nat(81u);
v___x_1783_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1784_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__0));
v___x_1785_ = l_mkPanicMessageWithDecl(v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__4(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__3));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__5(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0));
v___x_1790_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0));
v___x_1791_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__9(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__8));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1798_, lean_object* v_ctors_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v_env_1806_; lean_object* v___x_1807_; uint8_t v_isModule_1808_; lean_object* v___x_1809_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___x_2054_; uint8_t v___y_2056_; 
v___x_1805_ = lean_st_ref_get(v_a_1803_);
v_env_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_ref(v_env_1806_);
lean_dec(v___x_1805_);
v___x_1807_ = l_Lean_Environment_header(v_env_1806_);
v_isModule_1808_ = lean_ctor_get_uint8(v___x_1807_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_Lean_instInhabitedExpr;
v___x_2054_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__5, &l_Lean_Meta_mkSparseCasesOn___closed__5_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__5);
if (v_isModule_1808_ == 0)
{
v___y_2056_ = v_isModule_1808_;
goto v___jp_2055_;
}
else
{
uint8_t v_isExporting_2113_; 
v_isExporting_2113_ = lean_ctor_get_uint8(v_env_1806_, sizeof(void*)*8);
if (v_isExporting_2113_ == 0)
{
v___y_2056_ = v_isModule_1808_;
goto v___jp_2055_;
}
else
{
uint8_t v___x_2114_; 
v___x_2114_ = 0;
v___y_2056_ = v___x_2114_;
goto v___jp_2055_;
}
}
v___jp_1810_:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_ConstantInfo_levelParams(v___y_1817_);
if (lean_obj_tag(v___x_1828_) == 1)
{
lean_object* v_tail_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
v_tail_1829_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_tail_1829_);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_tail_1829_, v___x_1830_);
lean_inc_ref(v_ctors_1799_);
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 16, 9);
lean_closure_set(v___f_1832_, 0, v___y_1811_);
lean_closure_set(v___f_1832_, 1, v___x_1809_);
lean_closure_set(v___f_1832_, 2, v___y_1812_);
lean_closure_set(v___f_1832_, 3, v_ctors_1799_);
lean_closure_set(v___f_1832_, 4, v___y_1813_);
lean_closure_set(v___f_1832_, 5, v___x_1831_);
lean_closure_set(v___f_1832_, 6, v___y_1814_);
lean_closure_set(v___f_1832_, 7, v___y_1816_);
lean_closure_set(v___f_1832_, 8, v___y_1815_);
v___x_1833_ = l_Lean_ConstantInfo_type(v___y_1817_);
lean_dec_ref(v___y_1817_);
v___x_1834_ = 0;
v___x_1835_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v___x_1833_, v___f_1832_, v___x_1834_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_n(v_a_1836_, 2);
lean_dec_ref(v___x_1835_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
v___x_1837_ = lean_infer_type(v_a_1836_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1987_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_box(1);
lean_inc(v___y_1822_);
v___x_1840_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___y_1822_, v___x_1828_, v_a_1838_, v_a_1836_, v___x_1839_, v___y_1827_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1987_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1987_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 1);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_addDecl(v___x_1846_, v___x_1834_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v_nextMacroScope_1850_; lean_object* v_ngen_1851_; lean_object* v_auxDeclNGen_1852_; lean_object* v_traceState_1853_; lean_object* v_messages_1854_; lean_object* v_infoState_1855_; lean_object* v_snapshotTasks_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v___x_1847_);
v___x_1848_ = lean_st_ref_take(v___y_1827_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
v_nextMacroScope_1850_ = lean_ctor_get(v___x_1848_, 1);
v_ngen_1851_ = lean_ctor_get(v___x_1848_, 2);
v_auxDeclNGen_1852_ = lean_ctor_get(v___x_1848_, 3);
v_traceState_1853_ = lean_ctor_get(v___x_1848_, 4);
v_messages_1854_ = lean_ctor_get(v___x_1848_, 6);
v_infoState_1855_ = lean_ctor_get(v___x_1848_, 7);
v_snapshotTasks_1856_ = lean_ctor_get(v___x_1848_, 8);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1848_, 5);
lean_dec(v_unused_1977_);
v___x_1858_ = v___x_1848_;
v_isShared_1859_ = v_isSharedCheck_1976_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snapshotTasks_1856_);
lean_inc(v_infoState_1855_);
lean_inc(v_messages_1854_);
lean_inc(v_traceState_1853_);
lean_inc(v_auxDeclNGen_1852_);
lean_inc(v_ngen_1851_);
lean_inc(v_nextMacroScope_1850_);
lean_inc(v_env_1849_);
lean_dec(v___x_1848_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1976_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_inc_ref(v___y_1823_);
v___x_1860_ = l_Lean_EnvExtension_modifyState___redArg(v___y_1823_, v_env_1849_, v___y_1818_, v___y_1821_, v___y_1819_);
v___x_1861_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 5, v___x_1861_);
lean_ctor_set(v___x_1858_, 0, v___x_1860_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_nextMacroScope_1850_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_ngen_1851_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_auxDeclNGen_1852_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_traceState_1853_);
lean_ctor_set(v_reuseFailAlloc_1975_, 5, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1975_, 6, v_messages_1854_);
lean_ctor_set(v_reuseFailAlloc_1975_, 7, v_infoState_1855_);
lean_ctor_set(v_reuseFailAlloc_1975_, 8, v_snapshotTasks_1856_);
v___x_1863_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_mctx_1866_; lean_object* v_zetaDeltaFVarIds_1867_; lean_object* v_postponed_1868_; lean_object* v_diag_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1973_; 
v___x_1864_ = lean_st_ref_set(v___y_1827_, v___x_1863_);
v___x_1865_ = lean_st_ref_take(v___y_1825_);
v_mctx_1866_ = lean_ctor_get(v___x_1865_, 0);
v_zetaDeltaFVarIds_1867_ = lean_ctor_get(v___x_1865_, 2);
v_postponed_1868_ = lean_ctor_get(v___x_1865_, 3);
v_diag_1869_ = lean_ctor_get(v___x_1865_, 4);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1865_, 1);
lean_dec(v_unused_1974_);
v___x_1871_ = v___x_1865_;
v_isShared_1872_ = v_isSharedCheck_1973_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_diag_1869_);
lean_inc(v_postponed_1868_);
lean_inc(v_zetaDeltaFVarIds_1867_);
lean_inc(v_mctx_1866_);
lean_dec(v___x_1865_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1973_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_mctx_1866_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_zetaDeltaFVarIds_1867_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_postponed_1868_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_diag_1869_);
v___x_1875_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_env_1879_; lean_object* v_nextMacroScope_1880_; lean_object* v_ngen_1881_; lean_object* v_auxDeclNGen_1882_; lean_object* v_traceState_1883_; lean_object* v_messages_1884_; lean_object* v_infoState_1885_; lean_object* v_snapshotTasks_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1970_; 
v___x_1876_ = lean_st_ref_set(v___y_1825_, v___x_1875_);
lean_inc(v___y_1822_);
v___x_1877_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v___y_1822_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec_ref(v___x_1877_);
v___x_1878_ = lean_st_ref_take(v___y_1827_);
v_env_1879_ = lean_ctor_get(v___x_1878_, 0);
v_nextMacroScope_1880_ = lean_ctor_get(v___x_1878_, 1);
v_ngen_1881_ = lean_ctor_get(v___x_1878_, 2);
v_auxDeclNGen_1882_ = lean_ctor_get(v___x_1878_, 3);
v_traceState_1883_ = lean_ctor_get(v___x_1878_, 4);
v_messages_1884_ = lean_ctor_get(v___x_1878_, 6);
v_infoState_1885_ = lean_ctor_get(v___x_1878_, 7);
v_snapshotTasks_1886_ = lean_ctor_get(v___x_1878_, 8);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1878_, 5);
lean_dec(v_unused_1971_);
v___x_1888_ = v___x_1878_;
v_isShared_1889_ = v_isSharedCheck_1970_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snapshotTasks_1886_);
lean_inc(v_infoState_1885_);
lean_inc(v_messages_1884_);
lean_inc(v_traceState_1883_);
lean_inc(v_auxDeclNGen_1882_);
lean_inc(v_ngen_1881_);
lean_inc(v_nextMacroScope_1880_);
lean_inc(v_env_1879_);
lean_dec(v___x_1878_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1970_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_inc(v___y_1822_);
v___x_1890_ = l_Lean_markSparseCasesOn(v_env_1879_, v___y_1822_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 5, v___x_1861_);
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_nextMacroScope_1880_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_ngen_1881_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_auxDeclNGen_1882_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_traceState_1883_);
lean_ctor_set(v_reuseFailAlloc_1969_, 5, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1969_, 6, v_messages_1884_);
lean_ctor_set(v_reuseFailAlloc_1969_, 7, v_infoState_1885_);
lean_ctor_set(v_reuseFailAlloc_1969_, 8, v_snapshotTasks_1886_);
v___x_1892_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_mctx_1895_; lean_object* v_zetaDeltaFVarIds_1896_; lean_object* v_postponed_1897_; lean_object* v_diag_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1967_; 
v___x_1893_ = lean_st_ref_set(v___y_1827_, v___x_1892_);
v___x_1894_ = lean_st_ref_take(v___y_1825_);
v_mctx_1895_ = lean_ctor_get(v___x_1894_, 0);
v_zetaDeltaFVarIds_1896_ = lean_ctor_get(v___x_1894_, 2);
v_postponed_1897_ = lean_ctor_get(v___x_1894_, 3);
v_diag_1898_ = lean_ctor_get(v___x_1894_, 4);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1894_, 1);
lean_dec(v_unused_1968_);
v___x_1900_ = v___x_1894_;
v_isShared_1901_ = v_isSharedCheck_1967_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_diag_1898_);
lean_inc(v_postponed_1897_);
lean_inc(v_zetaDeltaFVarIds_1896_);
lean_inc(v_mctx_1895_);
lean_dec(v___x_1894_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1967_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_1873_);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_mctx_1895_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_zetaDeltaFVarIds_1896_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_postponed_1897_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_diag_1898_);
v___x_1903_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_env_1906_; lean_object* v_nextMacroScope_1907_; lean_object* v_ngen_1908_; lean_object* v_auxDeclNGen_1909_; lean_object* v_traceState_1910_; lean_object* v_messages_1911_; lean_object* v_infoState_1912_; lean_object* v_snapshotTasks_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1964_; 
v___x_1904_ = lean_st_ref_set(v___y_1825_, v___x_1903_);
v___x_1905_ = lean_st_ref_take(v___y_1827_);
v_env_1906_ = lean_ctor_get(v___x_1905_, 0);
v_nextMacroScope_1907_ = lean_ctor_get(v___x_1905_, 1);
v_ngen_1908_ = lean_ctor_get(v___x_1905_, 2);
v_auxDeclNGen_1909_ = lean_ctor_get(v___x_1905_, 3);
v_traceState_1910_ = lean_ctor_get(v___x_1905_, 4);
v_messages_1911_ = lean_ctor_get(v___x_1905_, 6);
v_infoState_1912_ = lean_ctor_get(v___x_1905_, 7);
v_snapshotTasks_1913_ = lean_ctor_get(v___x_1905_, 8);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v___x_1905_, 5);
lean_dec(v_unused_1965_);
v___x_1915_ = v___x_1905_;
v_isShared_1916_ = v_isSharedCheck_1964_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snapshotTasks_1913_);
lean_inc(v_infoState_1912_);
lean_inc(v_messages_1911_);
lean_inc(v_traceState_1910_);
lean_inc(v_auxDeclNGen_1909_);
lean_inc(v_ngen_1908_);
lean_inc(v_nextMacroScope_1907_);
lean_inc(v_env_1906_);
lean_dec(v___x_1905_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1964_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_numParams_1917_; lean_object* v_numIndices_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v_numParams_1917_ = lean_ctor_get(v___y_1820_, 1);
lean_inc(v_numParams_1917_);
v_numIndices_1918_ = lean_ctor_get(v___y_1820_, 2);
lean_inc(v_numIndices_1918_);
lean_dec_ref(v___y_1820_);
v___x_1919_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_nat_add(v_numParams_1917_, v___x_1920_);
lean_dec(v_numParams_1917_);
v___x_1922_ = lean_nat_add(v___x_1921_, v_numIndices_1918_);
lean_dec(v_numIndices_1918_);
lean_dec(v___x_1921_);
v___x_1923_ = lean_nat_add(v___x_1922_, v___x_1920_);
v___x_1924_ = lean_array_get_size(v_ctors_1799_);
v___x_1925_ = lean_nat_add(v___x_1923_, v___x_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_nat_add(v___x_1925_, v___x_1920_);
lean_dec(v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1927_, 0, v_indName_1798_);
lean_ctor_set(v___x_1927_, 1, v___x_1922_);
lean_ctor_set(v___x_1927_, 2, v___x_1926_);
lean_ctor_set(v___x_1927_, 3, v_ctors_1799_);
lean_inc(v___y_1822_);
v___x_1928_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1919_, v_env_1906_, v___y_1822_, v___x_1927_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 5, v___x_1861_);
lean_ctor_set(v___x_1915_, 0, v___x_1928_);
v___x_1930_ = v___x_1915_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_nextMacroScope_1907_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_ngen_1908_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_auxDeclNGen_1909_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_traceState_1910_);
lean_ctor_set(v_reuseFailAlloc_1963_, 5, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1963_, 6, v_messages_1911_);
lean_ctor_set(v_reuseFailAlloc_1963_, 7, v_infoState_1912_);
lean_ctor_set(v_reuseFailAlloc_1963_, 8, v_snapshotTasks_1913_);
v___x_1930_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_mctx_1933_; lean_object* v_zetaDeltaFVarIds_1934_; lean_object* v_postponed_1935_; lean_object* v_diag_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1961_; 
v___x_1931_ = lean_st_ref_set(v___y_1827_, v___x_1930_);
v___x_1932_ = lean_st_ref_take(v___y_1825_);
v_mctx_1933_ = lean_ctor_get(v___x_1932_, 0);
v_zetaDeltaFVarIds_1934_ = lean_ctor_get(v___x_1932_, 2);
v_postponed_1935_ = lean_ctor_get(v___x_1932_, 3);
v_diag_1936_ = lean_ctor_get(v___x_1932_, 4);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1932_, 1);
lean_dec(v_unused_1962_);
v___x_1938_ = v___x_1932_;
v_isShared_1939_ = v_isSharedCheck_1961_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_diag_1936_);
lean_inc(v_postponed_1935_);
lean_inc(v_zetaDeltaFVarIds_1934_);
lean_inc(v_mctx_1933_);
lean_dec(v___x_1932_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1961_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_1873_);
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_mctx_1933_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_zetaDeltaFVarIds_1934_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_postponed_1935_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_diag_1936_);
v___x_1941_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_st_ref_set(v___y_1825_, v___x_1941_);
lean_inc(v___y_1822_);
v___x_1943_ = l_Lean_enableRealizationsForConst(v___y_1822_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___y_1822_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___y_1822_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v___y_1822_);
v_a_1952_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
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
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_1978_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1847_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1847_);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___x_1828_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_1988_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1837_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1837_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___x_1828_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_1996_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1835_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1835_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v___x_1828_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v___x_2004_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_2005_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___x_2004_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_2005_;
}
}
v___jp_2006_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_inc(v_indName_1798_);
v___x_2020_ = l_Lean_mkCasesOnName(v_indName_1798_);
lean_inc(v___x_2020_);
v___x_2021_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v___x_2020_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_toConstantVal_2022_; lean_object* v_a_2023_; lean_object* v_levelParams_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_toConstantVal_2022_ = lean_ctor_get(v___y_2012_, 0);
v_a_2023_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2021_);
v_levelParams_2024_ = lean_ctor_get(v_toConstantVal_2022_, 1);
lean_inc(v_indName_1798_);
v___x_2025_ = l_mkCtorIdxName(v_indName_1798_);
v___x_2026_ = l_Lean_ConstantInfo_levelParams(v_a_2023_);
v___x_2027_ = l_List_lengthTR___redArg(v___x_2026_);
lean_dec(v___x_2026_);
v___x_2028_ = l_List_lengthTR___redArg(v_levelParams_2024_);
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = lean_nat_add(v___x_2028_, v___x_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_nat_dec_eq(v___x_2027_, v___x_2030_);
lean_dec(v___x_2030_);
lean_dec(v___x_2027_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v___x_2025_);
lean_dec(v_a_2023_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v___x_2032_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__4, &l_Lean_Meta_mkSparseCasesOn___closed__4_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__4);
v___x_2033_ = l_Lean_MessageData_ofConstName(v___x_2020_, v___x_2031_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2036_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_inc(v_a_2023_);
v___y_1811_ = v___y_2007_;
v___y_1812_ = v___y_2008_;
v___y_1813_ = v___x_2025_;
v___y_1814_ = v_a_2023_;
v___y_1815_ = v___x_2020_;
v___y_1816_ = v___y_2010_;
v___y_1817_ = v_a_2023_;
v___y_1818_ = v___y_2009_;
v___y_1819_ = v___y_2011_;
v___y_1820_ = v___y_2012_;
v___y_1821_ = v___y_2014_;
v___y_1822_ = v___y_2013_;
v___y_1823_ = v___y_2015_;
v___y_1824_ = v___y_2016_;
v___y_1825_ = v___y_2017_;
v___y_1826_ = v___y_2018_;
v___y_1827_ = v___y_2019_;
goto v___jp_1810_;
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v___x_2020_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_2046_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2021_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2021_);
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
v___jp_2055_:
{
lean_object* v___x_2057_; lean_object* v_asyncMode_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2057_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2058_ = lean_ctor_get(v___x_2057_, 2);
lean_inc_ref(v_ctors_1799_);
lean_inc(v_indName_1798_);
v___x_2059_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2059_, 0, v_indName_1798_);
lean_ctor_set(v___x_2059_, 1, v_ctors_1799_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*2, v___y_2056_);
v___x_2060_ = lean_box(0);
v___x_2061_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2054_, v___x_2057_, v_env_1806_, v_asyncMode_2058_, v___x_2060_);
v___x_2062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2061_, v___x_2059_);
lean_dec(v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 1)
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 0);
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_val_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_a_2073_; lean_object* v___x_2074_; 
lean_dec(v___x_2062_);
v___x_2071_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__7));
v___x_2072_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2071_, v_a_1803_);
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
lean_inc(v_indName_1798_);
v___x_2074_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_indName_1798_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; size_t v_sz_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = lean_box(0);
v_sz_2077_ = lean_array_size(v_ctors_1799_);
v___x_2078_ = ((size_t)0ULL);
lean_inc(v_indName_1798_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_2075_, v_indName_1798_, v_ctors_1799_, v_sz_2077_, v___x_2078_, v___x_2076_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_numParams_2080_; lean_object* v_numIndices_2081_; lean_object* v_ctors_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
lean_dec_ref(v___x_2079_);
v_numParams_2080_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_numParams_2080_);
v_numIndices_2081_ = lean_ctor_get(v_a_2075_, 2);
lean_inc(v_numIndices_2081_);
v_ctors_2082_ = lean_ctor_get(v_a_2075_, 4);
lean_inc(v_ctors_2082_);
lean_inc(v_a_2073_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2083_, 0, v___x_2059_);
lean_closure_set(v___f_2083_, 1, v_a_2073_);
v___x_2084_ = lean_array_get_size(v_ctors_1799_);
v___x_2085_ = l_List_lengthTR___redArg(v_ctors_2082_);
v___x_2086_ = lean_nat_dec_eq(v___x_2084_, v___x_2085_);
lean_dec(v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2007_ = v_numParams_2080_;
v___y_2008_ = v_numIndices_2081_;
v___y_2009_ = v___f_2083_;
v___y_2010_ = v_ctors_2082_;
v___y_2011_ = v___x_2060_;
v___y_2012_ = v_a_2075_;
v___y_2013_ = v_a_2073_;
v___y_2014_ = v_asyncMode_2058_;
v___y_2015_ = v___x_2057_;
v___y_2016_ = v_a_1800_;
v___y_2017_ = v_a_1801_;
v___y_2018_ = v_a_1802_;
v___y_2019_ = v_a_1803_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___f_2083_);
lean_dec(v_ctors_2082_);
lean_dec(v_numIndices_2081_);
lean_dec(v_numParams_2080_);
lean_dec(v_a_2075_);
lean_dec(v_a_2073_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v___x_2087_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__9, &l_Lean_Meta_mkSparseCasesOn___closed__9_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__9);
v___x_2088_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2087_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2075_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_2097_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2079_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2079_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_ctors_1799_);
lean_dec(v_indName_1798_);
v_a_2105_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2074_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2074_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2115_, lean_object* v_ctors_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2115_, v_ctors_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2127_, v_x_2128_, v_x_2129_);
lean_dec_ref(v_x_2129_);
lean_dec_ref(v_x_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2132_, v_x_2133_, v_x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object* v_00_u03b1_2136_, lean_object* v_name_2137_, uint8_t v_bi_2138_, lean_object* v_type_2139_, lean_object* v_k_2140_, uint8_t v_kind_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_2137_, v_bi_2138_, v_type_2139_, v_k_2140_, v_kind_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_name_2149_, lean_object* v_bi_2150_, lean_object* v_type_2151_, lean_object* v_k_2152_, lean_object* v_kind_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_bi_boxed_2159_; uint8_t v_kind_boxed_2160_; lean_object* v_res_2161_; 
v_bi_boxed_2159_ = lean_unbox(v_bi_2150_);
v_kind_boxed_2160_ = lean_unbox(v_kind_2153_);
v_res_2161_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(v_00_u03b1_2148_, v_name_2149_, v_bi_boxed_2159_, v_type_2151_, v_k_2152_, v_kind_boxed_2160_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, lean_object* v_type_2164_, lean_object* v_k_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_2163_, v_type_2164_, v_k_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_name_2173_, lean_object* v_type_2174_, lean_object* v_k_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_00_u03b1_2172_, v_name_2173_, v_type_2174_, v_k_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_00_u03b1_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_msg_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_00_u03b1_2190_, v_msg_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object* v_declName_2198_, uint8_t v_s_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_2198_, v_s_2199_, v___y_2201_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object* v_declName_2206_, lean_object* v_s_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
uint8_t v_s_boxed_2213_; lean_object* v_res_2214_; 
v_s_boxed_2213_ = lean_unbox(v_s_2207_);
v_res_2214_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(v_declName_2206_, v_s_boxed_2213_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2215_, lean_object* v_x_2216_, size_t v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2216_, v_x_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
size_t v_x_23967__boxed_2224_; lean_object* v_res_2225_; 
v_x_23967__boxed_2224_ = lean_unbox_usize(v_x_2222_);
lean_dec(v_x_2222_);
v_res_2225_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2220_, v_x_2221_, v_x_23967__boxed_2224_, v_x_2223_);
lean_dec_ref(v_x_2223_);
lean_dec_ref(v_x_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2226_, lean_object* v_x_2227_, size_t v_x_2228_, size_t v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2227_, v_x_2228_, v_x_2229_, v_x_2230_, v_x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
size_t v_x_23978__boxed_2239_; size_t v_x_23979__boxed_2240_; lean_object* v_res_2241_; 
v_x_23978__boxed_2239_ = lean_unbox_usize(v_x_2235_);
lean_dec(v_x_2235_);
v_x_23979__boxed_2240_ = lean_unbox_usize(v_x_2236_);
lean_dec(v_x_2236_);
v_res_2241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2233_, v_x_2234_, v_x_23978__boxed_2239_, v_x_23979__boxed_2240_, v_x_2237_, v_x_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object* v_00_u03b1_2242_, lean_object* v_constName_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2250_, lean_object* v_constName_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(v_00_u03b1_2250_, v_constName_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2258_, lean_object* v_keys_2259_, lean_object* v_vals_2260_, lean_object* v_heq_2261_, lean_object* v_i_2262_, lean_object* v_k_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_2259_, v_vals_2260_, v_i_2262_, v_k_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2265_, lean_object* v_keys_2266_, lean_object* v_vals_2267_, lean_object* v_heq_2268_, lean_object* v_i_2269_, lean_object* v_k_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(v_00_u03b2_2265_, v_keys_2266_, v_vals_2267_, v_heq_2268_, v_i_2269_, v_k_2270_);
lean_dec_ref(v_k_2270_);
lean_dec_ref(v_vals_2267_);
lean_dec_ref(v_keys_2266_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2272_, lean_object* v_n_2273_, lean_object* v_k_2274_, lean_object* v_v_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v_n_2273_, v_k_2274_, v_v_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2277_, size_t v_depth_2278_, lean_object* v_keys_2279_, lean_object* v_vals_2280_, lean_object* v_heq_2281_, lean_object* v_i_2282_, lean_object* v_entries_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_2278_, v_keys_2279_, v_vals_2280_, v_i_2282_, v_entries_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_depth_2286_, lean_object* v_keys_2287_, lean_object* v_vals_2288_, lean_object* v_heq_2289_, lean_object* v_i_2290_, lean_object* v_entries_2291_){
_start:
{
size_t v_depth_boxed_2292_; lean_object* v_res_2293_; 
v_depth_boxed_2292_ = lean_unbox_usize(v_depth_2286_);
lean_dec(v_depth_2286_);
v_res_2293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(v_00_u03b2_2285_, v_depth_boxed_2292_, v_keys_2287_, v_vals_2288_, v_heq_2289_, v_i_2290_, v_entries_2291_);
lean_dec_ref(v_vals_2288_);
lean_dec_ref(v_keys_2287_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object* v_00_u03b1_2294_, lean_object* v_ref_2295_, lean_object* v_constName_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_2295_, v_constName_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_ref_2304_, lean_object* v_constName_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(v_00_u03b1_2303_, v_ref_2304_, v_constName_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v_ref_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_x_2313_, v_x_2314_, v_x_2315_, v_x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object* v_00_u03b1_2318_, lean_object* v_ref_2319_, lean_object* v_msg_2320_, lean_object* v_declHint_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_2319_, v_msg_2320_, v_declHint_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_ref_2329_, lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(v_00_u03b1_2328_, v_ref_2329_, v_msg_2330_, v_declHint_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v_ref_2329_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object* v_msg_2338_, lean_object* v_declHint_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_2338_, v_declHint_2339_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object* v_msg_2346_, lean_object* v_declHint_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(v_msg_2346_, v_declHint_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object* v_00_u03b1_2354_, lean_object* v_ref_2355_, lean_object* v_msg_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_2355_, v_msg_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_ref_2364_, lean_object* v_msg_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(v_00_u03b1_2363_, v_ref_2364_, v_msg_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v_ref_2364_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2372_, lean_object* v_sparseCasesOnName_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v_toEnvExtension_2375_; lean_object* v_asyncMode_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2374_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2375_ = lean_ctor_get(v___x_2374_, 0);
v_asyncMode_2376_ = lean_ctor_get(v_toEnvExtension_2375_, 2);
v___x_2377_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2378_ = 0;
v___x_2379_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2377_, v___x_2374_, v_env_2372_, v_sparseCasesOnName_2373_, v_asyncMode_2376_, v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v_env_2384_; lean_object* v___x_2385_; lean_object* v_toEnvExtension_2386_; lean_object* v_asyncMode_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2383_ = lean_st_ref_get(v_a_2381_);
v_env_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc_ref(v_env_2384_);
lean_dec(v___x_2383_);
v___x_2385_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2386_ = lean_ctor_get(v___x_2385_, 0);
v_asyncMode_2387_ = lean_ctor_get(v_toEnvExtension_2386_, 2);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2389_ = 0;
v___x_2390_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2388_, v___x_2385_, v_env_2384_, v_sparseCasesOnName_2380_, v_asyncMode_2387_, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2392_, v_a_2393_);
lean_dec(v_a_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2396_, v_a_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2405_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_();
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
