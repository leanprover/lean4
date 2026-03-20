// Lean compiler output
// Module: Lean.Server.CodeActions.Attr
// Imports: public import Lean.Server.CodeActions.Basic import Lean.Compiler.IR.CompilerM
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CodeAction"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "HoleCodeAction"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 107, 254, 180, 191, 87, 213, 212)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkHoleCodeAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkHoleCodeAction___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "holeCodeActionExt"};
static const lean_object* l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 203, 29, 204, 182, 198, 37, 252)}};
static const lean_object* l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionExt;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CodeActions"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 109, 98, 186, 215, 54, 31, 240)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 81, 122, 157, 110, 139, 150, 137)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(140, 9, 218, 35, 21, 71, 196, 16)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 87, 198, 176, 47, 232, 96, 167)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(218, 76, 124, 25, 44, 216, 189, 65)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 13, 58, 95, 91, 219, 83, 153)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 153, 2, 234, 247, 5, 40, 80)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 5, 227, 15, 159, 154, 41, 231)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 131, 190, 193, 233, 215, 124, 132)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 208, 24, 91, 104, 151, 84, 140)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 80, 46, 201, 173, 200, 208, 35)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1824323934) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 77, 44, 66, 102, 234, 136, 182)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 50, 169, 217, 79, 205, 182, 252)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 130, 193, 32, 212, 119, 235, 154)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(42, 29, 14, 179, 205, 185, 16, 250)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "hole_code_action"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 9, 80, 177, 58, 188, 207, 158)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Declare a new hole code action, to appear in the code actions on \?_ and _"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "CommandCodeAction"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 81, 85, 177, 113, 119, 11, 211)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkCommandCodeAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkCommandCodeAction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0 = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value)}};
static const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1 = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActionEntry = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value;
static const lean_array_object l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0 = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value;
static const lean_ctor_object l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1 = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions = (const lean_object*)&l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_CommandCodeActions_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_CommandCodeActions_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_builtinCmdCodeActions;
LEAN_EXPORT lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_insertBuiltin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_array_object l_Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cmdCodeActionExt"};
static const lean_object* l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 243, 44, 165, 100, 218, 83, 102)}};
static const lean_object* l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionExt;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(249496773) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(39, 98, 82, 63, 230, 235, 167, 142)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 82, 115, 204, 119, 26, 186, 246)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 127, 98, 151, 84, 102, 70, 46)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(121, 217, 69, 124, 32, 57, 88, 239)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "command_code_action"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 247, 221, 42, 68, 92, 136, 34)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "Declare a new command code action, to appear in the code actions on commands"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "insertBuiltin"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 249, 157, 209, 61, 35, 44, 199)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23 = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Unexpected `command_code_action` attribute syntax"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1324802641) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(206, 142, 76, 87, 6, 108, 26, 136)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 33, 114, 77, 47, 114, 18, 64)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 97, 239, 179, 227, 241, 71, 55)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 195, 188, 80, 5, 62, 198, 198)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_command_code_action"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 66, 71, 193, 29, 122, 186, 70)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "Declare a new builtin command code action, to appear in the code actions on commands"};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(lean_object* v_n_8_, lean_object* v_env_9_, lean_object* v_opts_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3));
v___x_12_ = l_Lean_Environment_evalConstCheck___redArg(v_env_9_, v_opts_10_, v___x_11_, v_n_8_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___boxed(lean_object* v_n_13_, lean_object* v_env_14_, lean_object* v_opts_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(v_n_13_, v_env_14_, v_opts_15_);
lean_dec_ref(v_opts_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(lean_object* v_e_17_){
_start:
{
if (lean_obj_tag(v_e_17_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_a_19_ = lean_ctor_get(v_e_17_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v_e_17_);
if (v_isSharedCheck_27_ == 0)
{
v___x_21_ = v_e_17_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v_e_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_mk_io_user_error(v_a_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set_tag(v___x_21_, 1);
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v_e_17_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v_e_17_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v_e_17_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v_e_17_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set_tag(v___x_30_, 0);
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg___boxed(lean_object* v_e_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(lean_object* v_00_u03b1_39_, lean_object* v_e_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___boxed(lean_object* v_00_u03b1_43_, lean_object* v_e_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(v_00_u03b1_43_, v_e_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkHoleCodeAction(lean_object* v_n_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_env_50_; lean_object* v_opts_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_env_50_ = lean_ctor_get(v_a_48_, 0);
lean_inc_ref(v_env_50_);
v_opts_51_ = lean_ctor_get(v_a_48_, 1);
lean_inc_ref(v_opts_51_);
lean_dec_ref(v_a_48_);
v___x_52_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(v_n_47_, v_env_50_, v_opts_51_);
lean_dec_ref(v_opts_51_);
v___x_53_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkHoleCodeAction___boxed(lean_object* v_n_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_CodeAction_mkHoleCodeAction(v_n_54_, v_a_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v_x_58_){
_start:
{
lean_object* v_fst_59_; 
v_fst_59_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_fst_59_);
return v_fst_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_60_);
lean_dec_ref(v_x_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_64_);
lean_dec_ref(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v_x_66_, lean_object* v_s_67_, uint8_t v_x_68_){
_start:
{
lean_object* v_fst_69_; 
v_fst_69_ = lean_ctor_get(v_s_67_, 0);
lean_inc(v_fst_69_);
return v_fst_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v_x_70_, lean_object* v_s_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_x_2237__boxed_73_; lean_object* v_res_74_; 
v_x_2237__boxed_73_ = lean_unbox(v_x_72_);
v_res_74_ = l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_70_, v_s_71_, v_x_2237__boxed_73_);
lean_dec_ref(v_s_71_);
lean_dec_ref(v_x_70_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v_fst_77_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_fst_77_);
v_snd_78_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_snd_78_);
lean_dec_ref(v_x_75_);
v_fst_79_ = lean_ctor_get(v_x_76_, 0);
v_snd_80_ = lean_ctor_get(v_x_76_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_89_ == 0)
{
v___x_82_ = v_x_76_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_snd_80_);
lean_inc(v_fst_79_);
lean_dec(v_x_76_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = lean_array_push(v_fst_77_, v_fst_79_);
v___x_85_ = lean_array_push(v_snd_78_, v_snd_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v___x_85_);
lean_ctor_set(v___x_82_, 0, v___x_84_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_, lean_object* v_b_93_, lean_object* v___y_94_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_eq(v_i_91_, v_stop_92_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_array_uget_borrowed(v_as_90_, v_i_91_);
lean_inc_ref(v___y_94_);
lean_inc(v___x_97_);
v___x_98_ = l_Lean_CodeAction_mkHoleCodeAction(v___x_97_, v___y_94_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; size_t v___x_101_; size_t v___x_102_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_array_push(v_b_93_, v_a_99_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_91_, v___x_101_);
v_i_91_ = v___x_102_;
v_b_93_ = v___x_100_;
goto _start;
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v___y_94_);
lean_dec_ref(v_b_93_);
v_a_104_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_98_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_98_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v___x_112_; 
lean_dec_ref(v___y_94_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_b_93_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_113_, lean_object* v_i_114_, lean_object* v_stop_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_stop_boxed_120_; lean_object* v_res_121_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_115_);
lean_dec(v_stop_115_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v_as_113_, v_i_boxed_119_, v_stop_boxed_120_, v_b_116_, v___y_117_);
lean_dec_ref(v_as_113_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(lean_object* v_as_122_, size_t v_i_123_, size_t v_stop_124_, lean_object* v_b_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_a_129_; lean_object* v___y_134_; uint8_t v___x_136_; 
v___x_136_ = lean_usize_dec_eq(v_i_123_, v_stop_124_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_137_ = lean_array_uget_borrowed(v_as_122_, v_i_123_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_array_get_size(v___x_137_);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
v_a_129_ = v_b_125_;
goto v___jp_128_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = lean_nat_dec_le(v___x_139_, v___x_139_);
if (v___x_141_ == 0)
{
if (v___x_140_ == 0)
{
v_a_129_ = v_b_125_;
goto v___jp_128_;
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_139_);
lean_inc_ref(v___y_126_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v___x_137_, v___x_142_, v___x_143_, v_b_125_, v___y_126_);
v___y_134_ = v___x_144_;
goto v___jp_133_;
}
}
else
{
size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_139_);
lean_inc_ref(v___y_126_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v___x_137_, v___x_145_, v___x_146_, v_b_125_, v___y_126_);
v___y_134_ = v___x_147_;
goto v___jp_133_;
}
}
}
else
{
lean_object* v___x_148_; 
lean_dec_ref(v___y_126_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v_b_125_);
return v___x_148_;
}
v___jp_128_:
{
size_t v___x_130_; size_t v___x_131_; 
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_123_, v___x_130_);
v_i_123_ = v___x_131_;
v_b_125_ = v_a_129_;
goto _start;
}
v___jp_133_:
{
if (lean_obj_tag(v___y_134_) == 0)
{
lean_object* v_a_135_; 
v_a_135_ = lean_ctor_get(v___y_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref(v___y_134_);
v_a_129_ = v_a_135_;
goto v___jp_128_;
}
else
{
lean_dec_ref(v___y_126_);
return v___y_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_149_, lean_object* v_i_150_, lean_object* v_stop_151_, lean_object* v_b_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
size_t v_i_boxed_155_; size_t v_stop_boxed_156_; lean_object* v_res_157_; 
v_i_boxed_155_ = lean_unbox_usize(v_i_150_);
lean_dec(v_i_150_);
v_stop_boxed_156_ = lean_unbox_usize(v_stop_151_);
lean_dec(v_stop_151_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_149_, v_i_boxed_155_, v_stop_boxed_156_, v_b_152_, v___y_153_);
lean_dec_ref(v_as_149_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v___x_158_, lean_object* v___x_159_, lean_object* v___x_160_, lean_object* v_as_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_a_165_; lean_object* v___y_169_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_array_get_size(v_as_161_);
v___x_180_ = lean_nat_dec_lt(v___x_159_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec_ref(v___y_162_);
v_a_165_ = v___x_160_;
goto v___jp_164_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_le(v___x_179_, v___x_179_);
if (v___x_181_ == 0)
{
if (v___x_180_ == 0)
{
lean_dec_ref(v___y_162_);
v_a_165_ = v___x_160_;
goto v___jp_164_;
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_179_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_161_, v___x_182_, v___x_183_, v___x_160_, v___y_162_);
v___y_169_ = v___x_184_;
goto v___jp_168_;
}
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_179_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_161_, v___x_185_, v___x_186_, v___x_160_, v___y_162_);
v___y_169_ = v___x_187_;
goto v___jp_168_;
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_158_);
lean_ctor_set(v___x_166_, 1, v_a_165_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
v___jp_168_:
{
if (lean_obj_tag(v___y_169_) == 0)
{
lean_object* v_a_170_; 
v_a_170_ = lean_ctor_get(v___y_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref(v___y_169_);
v_a_165_ = v_a_170_;
goto v___jp_164_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v___x_158_);
v_a_171_ = lean_ctor_get(v___y_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___y_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___y_169_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___y_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v___x_190_, lean_object* v_as_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_188_, v___x_189_, v___x_190_, v_as_191_, v___y_192_);
lean_dec_ref(v_as_191_);
lean_dec(v___x_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(lean_object* v___x_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v___x_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_198_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___f_214_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___f_214_ = lean_alloc_closure((void*)(l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed), 6, 3);
lean_closure_set(v___f_214_, 0, v___x_213_);
lean_closure_set(v___f_214_, 1, v___x_212_);
lean_closure_set(v___f_214_, 2, v___x_213_);
return v___f_214_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_217_; lean_object* v___f_218_; 
v___x_217_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_218_, 0, v___x_217_);
return v___f_218_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_219_ = lean_box(0);
v___x_220_ = lean_box(2);
v___f_221_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___f_222_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___f_223_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___f_224_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_);
v___f_225_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_);
v___x_226_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___x_227_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___f_225_);
lean_ctor_set(v___x_227_, 2, v___f_224_);
lean_ctor_set(v___x_227_, 3, v___f_223_);
lean_ctor_set(v___x_227_, 4, v___f_222_);
lean_ctor_set(v___x_227_, 5, v___f_221_);
lean_ctor_set(v___x_227_, 6, v___x_220_);
lean_ctor_set(v___x_227_, 7, v___x_219_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___f_228_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_));
v___x_229_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___f_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_);
v___x_233_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
return v_res_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_236_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_ctor_set(v___x_241_, 3, v___x_239_);
lean_ctor_set(v___x_241_, 4, v___x_239_);
lean_ctor_set(v___x_241_, 5, v___x_239_);
lean_ctor_set(v___x_241_, 6, v___x_239_);
lean_ctor_set(v___x_241_, 7, v___x_239_);
lean_ctor_set(v___x_241_, 8, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_unsigned_to_nat(32u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_245_ = ((size_t)5ULL);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_unsigned_to_nat(32u);
v___x_248_ = lean_mk_empty_array_with_capacity(v___x_247_);
v___x_249_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_250_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_246_);
lean_ctor_set(v___x_250_, 3, v___x_246_);
lean_ctor_set_usize(v___x_250_, 4, v___x_245_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_box(1);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; lean_object* v_options_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v_options_261_ = lean_ctor_get(v___y_256_, 2);
v___x_262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_263_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_261_);
v___x_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_264_, 0, v_env_260_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
lean_ctor_set(v___x_264_, 3, v_options_261_);
v___x_265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_msgData_255_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msgData_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_ref_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_ref_276_ = lean_ctor_get(v___y_273_, 5);
v___x_277_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_272_, v___y_273_, v___y_274_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_inc(v_ref_276_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_ref_276_);
lean_ctor_set(v___x_282_, 1, v_a_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_304_, uint8_t v_kind_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___y_315_; 
v___x_309_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_310_ = l_Lean_MessageData_ofName(v_name_304_);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
switch(v_kind_305_)
{
case 0:
{
lean_object* v___x_322_; 
v___x_322_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_315_ = v___x_322_;
goto v___jp_314_;
}
case 1:
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7));
v___y_315_ = v___x_323_;
goto v___jp_314_;
}
default: 
{
lean_object* v___x_324_; 
v___x_324_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8));
v___y_315_ = v___x_324_;
goto v___jp_314_;
}
}
v___jp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_316_, 0, v___y_315_);
v___x_317_ = l_Lean_MessageData_ofFormat(v___x_316_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_313_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_320_, v___y_306_, v___y_307_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_325_, lean_object* v_kind_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_kind_boxed_330_; lean_object* v_res_331_; 
v_kind_boxed_330_ = lean_unbox(v_kind_326_);
v_res_331_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_325_, v_kind_boxed_330_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_decl_339_, lean_object* v_stx_340_, uint8_t v_kind_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___x_412_; 
lean_inc_ref(v___y_342_);
v___x_412_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_340_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_412_) == 0)
{
uint8_t v___x_413_; uint8_t v___x_414_; 
lean_dec_ref(v___x_412_);
v___x_413_ = 0;
v___x_414_ = l_Lean_instBEqAttributeKind_beq(v_kind_341_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v_decl_339_);
lean_dec(v___x_338_);
v___x_415_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_337_, v_kind_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v___x_415_;
}
else
{
v___y_346_ = v___y_342_;
v___y_347_ = v___y_343_;
goto v___jp_345_;
}
}
else
{
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v_decl_339_);
lean_dec(v___x_338_);
lean_dec(v___x_337_);
return v___x_412_;
}
v___jp_345_:
{
lean_object* v___x_348_; 
lean_inc(v___y_347_);
lean_inc_ref(v___y_346_);
lean_inc(v_decl_339_);
v___x_348_ = l_Lean_ensureAttrDeclIsMeta(v___x_337_, v_decl_339_, v_kind_341_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_410_; 
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_348_, 0);
lean_dec(v_unused_411_);
v___x_350_ = v___x_348_;
v_isShared_351_ = v_isSharedCheck_410_;
goto v_resetjp_349_;
}
else
{
lean_dec(v___x_348_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_410_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v___x_354_; 
v___x_352_ = lean_st_ref_get(v___y_347_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_env_353_);
lean_dec(v___x_352_);
lean_inc(v_decl_339_);
v___x_354_ = lean_decl_get_sorry_dep(v_env_353_, v_decl_339_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; lean_object* v_env_356_; lean_object* v_options_357_; lean_object* v_ref_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_del_object(v___x_350_);
v___x_355_ = lean_st_ref_get(v___y_347_);
v_env_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_env_356_);
lean_dec(v___x_355_);
v_options_357_ = lean_ctor_get(v___y_346_, 2);
lean_inc_ref(v_options_357_);
v_ref_358_ = lean_ctor_get(v___y_346_, 5);
lean_inc(v_ref_358_);
lean_dec_ref(v___y_346_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_env_356_);
lean_ctor_set(v___x_359_, 1, v_options_357_);
lean_inc(v_decl_339_);
v___x_360_ = l_Lean_CodeAction_mkHoleCodeAction(v_decl_339_, v___x_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_ref_358_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_393_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_393_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_393_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_auxDeclNGen_369_; lean_object* v_traceState_370_; lean_object* v_messages_371_; lean_object* v_infoState_372_; lean_object* v_snapshotTasks_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_391_; 
v___x_365_ = lean_st_ref_take(v___y_347_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
v_nextMacroScope_367_ = lean_ctor_get(v___x_365_, 1);
v_ngen_368_ = lean_ctor_get(v___x_365_, 2);
v_auxDeclNGen_369_ = lean_ctor_get(v___x_365_, 3);
v_traceState_370_ = lean_ctor_get(v___x_365_, 4);
v_messages_371_ = lean_ctor_get(v___x_365_, 6);
v_infoState_372_ = lean_ctor_get(v___x_365_, 7);
v_snapshotTasks_373_ = lean_ctor_get(v___x_365_, 8);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_365_, 5);
lean_dec(v_unused_392_);
v___x_375_ = v___x_365_;
v_isShared_376_ = v_isSharedCheck_391_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_snapshotTasks_373_);
lean_inc(v_infoState_372_);
lean_inc(v_messages_371_);
lean_inc(v_traceState_370_);
lean_inc(v_auxDeclNGen_369_);
lean_inc(v_ngen_368_);
lean_inc(v_nextMacroScope_367_);
lean_inc(v_env_366_);
lean_dec(v___x_365_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_391_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v_toEnvExtension_378_; lean_object* v_asyncMode_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_377_ = l_Lean_CodeAction_holeCodeActionExt;
v_toEnvExtension_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_toEnvExtension_378_);
v_asyncMode_379_ = lean_ctor_get(v_toEnvExtension_378_, 2);
lean_inc(v_asyncMode_379_);
lean_dec_ref(v_toEnvExtension_378_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_decl_339_);
lean_ctor_set(v___x_380_, 1, v_a_361_);
v___x_381_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_377_, v_env_366_, v___x_380_, v_asyncMode_379_, v___x_338_);
lean_dec(v_asyncMode_379_);
v___x_382_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 5, v___x_382_);
lean_ctor_set(v___x_375_, 0, v___x_381_);
v___x_384_ = v___x_375_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_auxDeclNGen_369_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_traceState_370_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 6, v_messages_371_);
lean_ctor_set(v_reuseFailAlloc_390_, 7, v_infoState_372_);
lean_ctor_set(v_reuseFailAlloc_390_, 8, v_snapshotTasks_373_);
v___x_384_ = v_reuseFailAlloc_390_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = lean_st_ref_set(v___y_347_, v___x_384_);
lean_dec(v___y_347_);
v___x_386_ = lean_box(0);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_386_);
v___x_388_ = v___x_363_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_405_; 
lean_dec(v___y_347_);
lean_dec(v_decl_339_);
lean_dec(v___x_338_);
v_a_394_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_405_ == 0)
{
v___x_396_ = v___x_360_;
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_360_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_398_ = lean_io_error_to_string(v_a_394_);
v___x_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = l_Lean_MessageData_ofFormat(v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_ref_358_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_401_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
lean_dec_ref(v___x_354_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_decl_339_);
lean_dec(v___x_338_);
v___x_406_ = lean_box(0);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_406_);
v___x_408_ = v___x_350_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
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
else
{
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_decl_339_);
lean_dec(v___x_338_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v_decl_418_, lean_object* v_stx_419_, lean_object* v_kind_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_kind_boxed_424_; lean_object* v_res_425_; 
v_kind_boxed_424_ = lean_unbox(v_kind_420_);
v_res_425_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_416_, v___x_417_, v_decl_418_, v_stx_419_, v_kind_boxed_424_, v___y_421_, v___y_422_);
return v_res_425_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(lean_object* v___x_432_, lean_object* v_decl_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_438_ = l_Lean_MessageData_ofName(v___x_432_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_441_, v___y_434_, v___y_435_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object* v___x_443_, lean_object* v_decl_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_443_, v_decl_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v_decl_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_));
v___x_531_ = l_Lean_registerBuiltinAttribute(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_534_, lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_535_, v___y_536_, v___y_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(v_00_u03b1_540_, v_msg_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_546_, lean_object* v_name_547_, uint8_t v_kind_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_547_, v_kind_548_, v___y_549_, v___y_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_553_, lean_object* v_name_554_, lean_object* v_kind_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_kind_boxed_559_; lean_object* v_res_560_; 
v_kind_boxed_559_ = lean_unbox(v_kind_555_);
v_res_560_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(v_00_u03b1_553_, v_name_554_, v_kind_boxed_559_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(lean_object* v_n_566_, lean_object* v_env_567_, lean_object* v_opts_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1));
v___x_570_ = l_Lean_Environment_evalConstCheck___redArg(v_env_567_, v_opts_568_, v___x_569_, v_n_566_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___boxed(lean_object* v_n_571_, lean_object* v_env_572_, lean_object* v_opts_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(v_n_571_, v_env_572_, v_opts_573_);
lean_dec_ref(v_opts_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkCommandCodeAction(lean_object* v_n_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_env_578_; lean_object* v_opts_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_env_578_ = lean_ctor_get(v_a_576_, 0);
lean_inc_ref(v_env_578_);
v_opts_579_ = lean_ctor_get(v_a_576_, 1);
lean_inc_ref(v_opts_579_);
lean_dec_ref(v_a_576_);
v___x_580_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(v_n_575_, v_env_578_, v_opts_579_);
lean_dec_ref(v_opts_579_);
v___x_581_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_mkCommandCodeAction___boxed(lean_object* v_n_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_CodeAction_mkCommandCodeAction(v_n_582_, v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(lean_object* v_t_600_, lean_object* v_k_601_, lean_object* v_fallback_602_){
_start:
{
if (lean_obj_tag(v_t_600_) == 0)
{
lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v_l_605_; lean_object* v_r_606_; uint8_t v___x_607_; 
v_k_603_ = lean_ctor_get(v_t_600_, 1);
v_v_604_ = lean_ctor_get(v_t_600_, 2);
v_l_605_ = lean_ctor_get(v_t_600_, 3);
v_r_606_ = lean_ctor_get(v_t_600_, 4);
v___x_607_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_601_, v_k_603_);
switch(v___x_607_)
{
case 0:
{
v_t_600_ = v_l_605_;
goto _start;
}
case 1:
{
lean_inc(v_v_604_);
return v_v_604_;
}
default: 
{
v_t_600_ = v_r_606_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_602_);
return v_fallback_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg___boxed(lean_object* v_t_610_, lean_object* v_k_611_, lean_object* v_fallback_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_610_, v_k_611_, v_fallback_612_);
lean_dec(v_fallback_612_);
lean_dec(v_k_611_);
lean_dec(v_t_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(lean_object* v_action_616_, lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_, lean_object* v_b_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; 
v___x_622_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0));
v___x_624_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_b_620_, v___x_622_, v___x_623_);
lean_inc_ref(v_action_616_);
v___x_625_ = lean_array_push(v___x_624_, v_action_616_);
lean_inc(v___x_622_);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_622_, v___x_625_, v_b_620_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_618_, v___x_627_);
v_i_618_ = v___x_628_;
v_b_620_ = v___x_626_;
goto _start;
}
else
{
lean_dec_ref(v_action_616_);
return v_b_620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___boxed(lean_object* v_action_630_, lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_, lean_object* v_b_634_){
_start:
{
size_t v_i_boxed_635_; size_t v_stop_boxed_636_; lean_object* v_res_637_; 
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_636_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_630_, v_as_631_, v_i_boxed_635_, v_stop_boxed_636_, v_b_634_);
lean_dec_ref(v_as_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_CommandCodeActions_insert(lean_object* v_self_638_, lean_object* v_tacticKinds_639_, lean_object* v_action_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_array_get_size(v_tacticKinds_639_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_nat_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v_onAnyCmd_644_; lean_object* v_onCmd_645_; uint8_t v___x_646_; 
v_onAnyCmd_644_ = lean_ctor_get(v_self_638_, 0);
v_onCmd_645_ = lean_ctor_get(v_self_638_, 1);
v___x_646_ = lean_nat_dec_lt(v___x_642_, v___x_641_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_action_640_);
return v_self_638_;
}
else
{
uint8_t v___x_647_; 
v___x_647_ = lean_nat_dec_le(v___x_641_, v___x_641_);
if (v___x_647_ == 0)
{
if (v___x_646_ == 0)
{
lean_dec_ref(v_action_640_);
return v_self_638_;
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_657_; 
lean_inc(v_onCmd_645_);
lean_inc_ref(v_onAnyCmd_644_);
v_isSharedCheck_657_ = !lean_is_exclusive(v_self_638_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_self_638_, 1);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_self_638_, 0);
lean_dec(v_unused_659_);
v___x_649_ = v_self_638_;
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_self_638_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_641_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_640_, v_tacticKinds_639_, v___x_651_, v___x_652_, v_onCmd_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_653_);
v___x_655_ = v___x_649_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_onAnyCmd_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
lean_inc(v_onCmd_645_);
lean_inc_ref(v_onAnyCmd_644_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_self_638_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_670_ = lean_ctor_get(v_self_638_, 1);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_self_638_, 0);
lean_dec(v_unused_671_);
v___x_661_ = v_self_638_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_self_638_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_641_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_640_, v_tacticKinds_639_, v___x_663_, v___x_664_, v_onCmd_645_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_665_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_onAnyCmd_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
else
{
lean_object* v_onAnyCmd_672_; lean_object* v_onCmd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_onAnyCmd_672_ = lean_ctor_get(v_self_638_, 0);
v_onCmd_673_ = lean_ctor_get(v_self_638_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_self_638_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v_self_638_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_onCmd_673_);
lean_inc(v_onAnyCmd_672_);
lean_dec(v_self_638_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_array_push(v_onAnyCmd_672_, v_action_640_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_onCmd_673_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_CommandCodeActions_insert___boxed(lean_object* v_self_682_, lean_object* v_tacticKinds_683_, lean_object* v_action_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_CodeAction_CommandCodeActions_insert(v_self_682_, v_tacticKinds_683_, v_action_684_);
lean_dec_ref(v_tacticKinds_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(lean_object* v_00_u03b4_686_, lean_object* v_t_687_, lean_object* v_k_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_687_, v_k_688_, v_fallback_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___boxed(lean_object* v_00_u03b4_691_, lean_object* v_t_692_, lean_object* v_k_693_, lean_object* v_fallback_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(v_00_u03b4_691_, v_t_692_, v_k_693_, v_fallback_694_);
lean_dec(v_fallback_694_);
lean_dec(v_k_693_);
lean_dec(v_t_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((lean_object*)(l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1));
v___x_698_ = lean_st_mk_ref(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2____boxed(lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_insertBuiltin(lean_object* v_args_702_, lean_object* v_proc_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_705_ = l_Lean_CodeAction_builtinCmdCodeActions;
v___x_706_ = lean_st_ref_take(v___x_705_);
v___x_707_ = l_Lean_CodeAction_CommandCodeActions_insert(v___x_706_, v_args_702_, v_proc_703_);
v___x_708_ = lean_st_ref_set(v___x_705_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_insertBuiltin___boxed(lean_object* v_args_710_, lean_object* v_proc_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_CodeAction_insertBuiltin(v_args_710_, v_proc_711_);
lean_dec_ref(v_args_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v_x_714_){
_start:
{
lean_object* v_fst_715_; 
v_fst_715_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_fst_715_);
return v_fst_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_716_);
lean_dec_ref(v_x_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_720_);
lean_dec_ref(v_x_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v_x_722_, lean_object* v_s_723_, uint8_t v_x_724_){
_start:
{
lean_object* v_fst_725_; 
v_fst_725_ = lean_ctor_get(v_s_723_, 0);
lean_inc(v_fst_725_);
return v_fst_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v_x_726_, lean_object* v_s_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_x_2826__boxed_729_; lean_object* v_res_730_; 
v_x_2826__boxed_729_ = lean_unbox(v_x_728_);
v_res_730_ = l_Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_726_, v_s_727_, v_x_2826__boxed_729_);
lean_dec_ref(v_s_727_);
lean_dec_ref(v_x_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_fst_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_fst_733_ = lean_ctor_get(v_x_732_, 0);
lean_inc(v_fst_733_);
v_fst_734_ = lean_ctor_get(v_x_731_, 0);
lean_inc(v_fst_734_);
v_snd_735_ = lean_ctor_get(v_x_731_, 1);
lean_inc(v_snd_735_);
lean_dec_ref(v_x_731_);
v_snd_736_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_x_732_, 0);
lean_dec(v_unused_747_);
v___x_738_ = v_x_732_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_dec(v_x_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_cmdKinds_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_cmdKinds_740_ = lean_ctor_get(v_fst_733_, 1);
lean_inc_ref(v_cmdKinds_740_);
v___x_741_ = lean_array_push(v_fst_734_, v_fst_733_);
v___x_742_ = l_Lean_CodeAction_CommandCodeActions_insert(v_snd_735_, v_cmdKinds_740_, v_snd_736_);
lean_dec_ref(v_cmdKinds_740_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_742_);
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v___x_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lean_st_ref_get(v___x_750_);
v___x_753_ = ((lean_object*)(l_Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v___x_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_756_);
lean_dec(v___x_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v_declName_767_; lean_object* v_cmdKinds_768_; lean_object* v___x_769_; 
v___x_766_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
v_declName_767_ = lean_ctor_get(v___x_766_, 0);
v_cmdKinds_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc_ref(v___y_763_);
lean_inc(v_declName_767_);
v___x_769_ = l_Lean_CodeAction_mkCommandCodeAction(v_declName_767_, v___y_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; size_t v___x_772_; size_t v___x_773_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v___x_771_ = l_Lean_CodeAction_CommandCodeActions_insert(v_b_762_, v_cmdKinds_768_, v_a_770_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_760_, v___x_772_);
v_i_760_ = v___x_773_;
v_b_762_ = v___x_771_;
goto _start;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v___y_763_);
lean_dec_ref(v_b_762_);
v_a_775_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_769_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
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
lean_object* v___x_783_; 
lean_dec_ref(v___y_763_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_b_762_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_784_, lean_object* v_i_785_, lean_object* v_stop_786_, lean_object* v_b_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v_i_boxed_790_ = lean_unbox_usize(v_i_785_);
lean_dec(v_i_785_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_786_);
lean_dec(v_stop_786_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v_as_784_, v_i_boxed_790_, v_stop_boxed_791_, v_b_787_, v___y_788_);
lean_dec_ref(v_as_784_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(lean_object* v_as_793_, size_t v_i_794_, size_t v_stop_795_, lean_object* v_b_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_a_800_; lean_object* v___y_805_; uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_eq(v_i_794_, v_stop_795_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_808_ = lean_array_uget_borrowed(v_as_793_, v_i_794_);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_array_get_size(v___x_808_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
v_a_800_ = v_b_796_;
goto v___jp_799_;
}
else
{
uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_le(v___x_810_, v___x_810_);
if (v___x_812_ == 0)
{
if (v___x_811_ == 0)
{
v_a_800_ = v_b_796_;
goto v___jp_799_;
}
else
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_810_);
lean_inc_ref(v___y_797_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v___x_808_, v___x_813_, v___x_814_, v_b_796_, v___y_797_);
v___y_805_ = v___x_815_;
goto v___jp_804_;
}
}
else
{
size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((size_t)0ULL);
v___x_817_ = lean_usize_of_nat(v___x_810_);
lean_inc_ref(v___y_797_);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v___x_808_, v___x_816_, v___x_817_, v_b_796_, v___y_797_);
v___y_805_ = v___x_818_;
goto v___jp_804_;
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec_ref(v___y_797_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_b_796_);
return v___x_819_;
}
v___jp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_794_, v___x_801_);
v_i_794_ = v___x_802_;
v_b_796_ = v_a_800_;
goto _start;
}
v___jp_804_:
{
if (lean_obj_tag(v___y_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___y_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___y_805_);
v_a_800_ = v_a_806_;
goto v___jp_799_;
}
else
{
lean_dec_ref(v___y_797_);
return v___y_805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_820_, lean_object* v_i_821_, lean_object* v_stop_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_i_boxed_826_; size_t v_stop_boxed_827_; lean_object* v_res_828_; 
v_i_boxed_826_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_stop_boxed_827_ = lean_unbox_usize(v_stop_822_);
lean_dec(v_stop_822_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_820_, v_i_boxed_826_, v_stop_boxed_827_, v_b_823_, v___y_824_);
lean_dec_ref(v_as_820_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(lean_object* v___x_829_, lean_object* v_as_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_a_836_; lean_object* v___y_841_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_833_ = lean_st_ref_get(v___x_829_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_array_get_size(v_as_830_);
v___x_852_ = lean_nat_dec_lt(v___x_834_, v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v___y_831_);
v_a_836_ = v___x_833_;
goto v___jp_835_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = lean_nat_dec_le(v___x_851_, v___x_851_);
if (v___x_853_ == 0)
{
if (v___x_852_ == 0)
{
lean_dec_ref(v___y_831_);
v_a_836_ = v___x_833_;
goto v___jp_835_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_851_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_830_, v___x_854_, v___x_855_, v___x_833_, v___y_831_);
v___y_841_ = v___x_856_;
goto v___jp_840_;
}
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_851_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_830_, v___x_857_, v___x_858_, v___x_833_, v___y_831_);
v___y_841_ = v___x_859_;
goto v___jp_840_;
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_a_836_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
v___jp_840_:
{
if (lean_obj_tag(v___y_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___y_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___y_841_);
v_a_836_ = v_a_842_;
goto v___jp_835_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___y_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___y_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___y_841_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___y_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v___x_860_, lean_object* v_as_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_860_, v_as_861_, v___y_862_);
lean_dec_ref(v_as_861_);
lean_dec(v___x_860_);
return v_res_864_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___f_875_; 
v___x_874_ = l_Lean_CodeAction_builtinCmdCodeActions;
v___f_875_ = lean_alloc_closure((void*)(l_Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_875_, 0, v___x_874_);
return v___f_875_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; lean_object* v___f_877_; 
v___x_876_ = l_Lean_CodeAction_builtinCmdCodeActions;
v___f_877_ = lean_alloc_closure((void*)(l_Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_877_, 0, v___x_876_);
return v___f_877_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_878_ = lean_box(0);
v___x_879_ = lean_box(2);
v___f_880_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___f_881_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___f_882_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___f_883_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
v___f_884_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
v___x_885_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___x_886_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___f_884_);
lean_ctor_set(v___x_886_, 2, v___f_883_);
lean_ctor_set(v___x_886_, 3, v___f_882_);
lean_ctor_set(v___x_886_, 4, v___f_881_);
lean_ctor_set(v___x_886_, 5, v___f_880_);
lean_ctor_set(v___x_886_, 6, v___x_879_);
lean_ctor_set(v___x_886_, 7, v___x_878_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___f_887_ = ((lean_object*)(l_Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_));
v___x_888_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___f_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_, &l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once, _init_l_Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
v___x_892_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
return v_res_894_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_keys_895_, lean_object* v_i_896_, lean_object* v_k_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_array_get_size(v_keys_895_);
v___x_899_ = lean_nat_dec_lt(v_i_896_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec(v_i_896_);
return v___x_899_;
}
else
{
lean_object* v_k_x27_900_; uint8_t v___x_901_; 
v_k_x27_900_ = lean_array_fget_borrowed(v_keys_895_, v_i_896_);
v___x_901_ = l_Lean_instBEqExtraModUse_beq(v_k_897_, v_k_x27_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_i_896_, v___x_902_);
lean_dec(v_i_896_);
v_i_896_ = v___x_903_;
goto _start;
}
else
{
lean_dec(v_i_896_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_keys_905_, lean_object* v_i_906_, lean_object* v_k_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg(v_keys_905_, v_i_906_, v_k_907_);
lean_dec_ref(v_k_907_);
lean_dec_ref(v_keys_905_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; 
v___x_910_ = ((size_t)5ULL);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_shift_left(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; 
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_915_ = lean_usize_sub(v___x_914_, v___x_913_);
return v___x_915_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_916_, size_t v_x_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_es_919_; lean_object* v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v_j_924_; lean_object* v___x_925_; 
v_es_919_ = lean_ctor_get(v_x_916_, 0);
lean_inc_ref(v_es_919_);
lean_dec_ref(v_x_916_);
v___x_920_ = lean_box(2);
v___x_921_ = ((size_t)5ULL);
v___x_922_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_923_ = lean_usize_land(v_x_917_, v___x_922_);
v_j_924_ = lean_usize_to_nat(v___x_923_);
v___x_925_ = lean_array_get(v___x_920_, v_es_919_, v_j_924_);
lean_dec(v_j_924_);
lean_dec_ref(v_es_919_);
switch(lean_obj_tag(v___x_925_))
{
case 0:
{
lean_object* v_key_926_; uint8_t v___x_927_; 
v_key_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_key_926_);
lean_dec_ref(v___x_925_);
v___x_927_ = l_Lean_instBEqExtraModUse_beq(v_x_918_, v_key_926_);
lean_dec(v_key_926_);
return v___x_927_;
}
case 1:
{
lean_object* v_node_928_; size_t v___x_929_; 
v_node_928_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_node_928_);
lean_dec_ref(v___x_925_);
v___x_929_ = lean_usize_shift_right(v_x_917_, v___x_921_);
v_x_916_ = v_node_928_;
v_x_917_ = v___x_929_;
goto _start;
}
default: 
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
}
else
{
lean_object* v_ks_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_ks_932_ = lean_ctor_get(v_x_916_, 0);
lean_inc_ref(v_ks_932_);
lean_dec_ref(v_x_916_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg(v_ks_932_, v___x_933_, v_x_918_);
lean_dec_ref(v_ks_932_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
size_t v_x_6292__boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_x_6292__boxed_938_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_935_, v_x_6292__boxed_938_, v_x_937_);
lean_dec_ref(v_x_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint64_t v___x_943_; size_t v___x_944_; uint8_t v___x_945_; 
v___x_943_ = l_Lean_instHashableExtraModUse_hash(v_x_942_);
v___x_944_ = lean_uint64_to_usize(v___x_943_);
v___x_945_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_941_, v___x_944_, v_x_942_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_946_, v_x_947_);
lean_dec_ref(v_x_947_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_950_; double v___x_951_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_float_of_nat(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4(lean_object* v_cls_955_, lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_ref_960_; lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1006_; 
v_ref_960_ = lean_ctor_get(v___y_957_, 5);
v___x_961_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_956_, v___y_957_, v___y_958_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_1006_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1006_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v_traceState_967_; lean_object* v_env_968_; lean_object* v_nextMacroScope_969_; lean_object* v_ngen_970_; lean_object* v_auxDeclNGen_971_; lean_object* v_cache_972_; lean_object* v_messages_973_; lean_object* v_infoState_974_; lean_object* v_snapshotTasks_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1005_; 
v___x_966_ = lean_st_ref_take(v___y_958_);
v_traceState_967_ = lean_ctor_get(v___x_966_, 4);
v_env_968_ = lean_ctor_get(v___x_966_, 0);
v_nextMacroScope_969_ = lean_ctor_get(v___x_966_, 1);
v_ngen_970_ = lean_ctor_get(v___x_966_, 2);
v_auxDeclNGen_971_ = lean_ctor_get(v___x_966_, 3);
v_cache_972_ = lean_ctor_get(v___x_966_, 5);
v_messages_973_ = lean_ctor_get(v___x_966_, 6);
v_infoState_974_ = lean_ctor_get(v___x_966_, 7);
v_snapshotTasks_975_ = lean_ctor_get(v___x_966_, 8);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_977_ = v___x_966_;
v_isShared_978_ = v_isSharedCheck_1005_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snapshotTasks_975_);
lean_inc(v_infoState_974_);
lean_inc(v_messages_973_);
lean_inc(v_cache_972_);
lean_inc(v_traceState_967_);
lean_inc(v_auxDeclNGen_971_);
lean_inc(v_ngen_970_);
lean_inc(v_nextMacroScope_969_);
lean_inc(v_env_968_);
lean_dec(v___x_966_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1005_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint64_t v_tid_979_; lean_object* v_traces_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1004_; 
v_tid_979_ = lean_ctor_get_uint64(v_traceState_967_, sizeof(void*)*1);
v_traces_980_ = lean_ctor_get(v_traceState_967_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_traceState_967_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_982_ = v_traceState_967_;
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_traces_980_);
lean_dec(v_traceState_967_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; double v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_984_ = lean_box(0);
v___x_985_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__0);
v___x_986_ = 0;
v___x_987_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__1));
v___x_988_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_988_, 0, v_cls_955_);
lean_ctor_set(v___x_988_, 1, v___x_984_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
lean_ctor_set_float(v___x_988_, sizeof(void*)*3, v___x_985_);
lean_ctor_set_float(v___x_988_, sizeof(void*)*3 + 8, v___x_985_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*3 + 16, v___x_986_);
v___x_989_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__2));
v___x_990_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v_a_962_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
lean_inc(v_ref_960_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_ref_960_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_PersistentArray_push___redArg(v_traces_980_, v___x_991_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_992_);
v___x_994_ = v___x_982_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_992_);
lean_ctor_set_uint64(v_reuseFailAlloc_1003_, sizeof(void*)*1, v_tid_979_);
v___x_994_ = v_reuseFailAlloc_1003_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v___x_994_);
v___x_996_ = v___x_977_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_env_968_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_nextMacroScope_969_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ngen_970_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_auxDeclNGen_971_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_cache_972_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_messages_973_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_infoState_974_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v_snapshotTasks_975_);
v___x_996_ = v_reuseFailAlloc_1002_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_st_ref_set(v___y_958_, v___x_996_);
v___x_998_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_998_);
v___x_1000_ = v___x_964_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___boxed(lean_object* v_cls_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4(v_cls_1007_, v_msg_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg(lean_object* v_cls_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_options_1019_; uint8_t v_hasTrace_1020_; 
v_options_1019_ = lean_ctor_get(v___y_1017_, 2);
v_hasTrace_1020_ = lean_ctor_get_uint8(v_options_1019_, sizeof(void*)*1);
if (v_hasTrace_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_cls_1016_);
v___x_1021_ = lean_box(v_hasTrace_1020_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
else
{
lean_object* v_inheritedTraceOptions_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_inheritedTraceOptions_1023_ = lean_ctor_get(v___y_1017_, 13);
v___x_1024_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1025_ = l_Lean_Name_append(v___x_1024_, v_cls_1016_);
v___x_1026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1023_, v_options_1019_, v___x_1025_);
lean_dec(v___x_1025_);
v___x_1027_ = lean_box(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_cls_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg(v_cls_1029_, v___y_1030_);
lean_dec_ref(v___y_1030_);
return v_res_1032_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1));
v___x_1036_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0));
v___x_1037_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1036_, v___x_1035_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4___closed__1));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_mod_1059_, uint8_t v_isMeta_1060_, lean_object* v_hint_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_env_1066_; uint8_t v_isExporting_1067_; lean_object* v___x_1068_; lean_object* v_env_1069_; lean_object* v___x_1070_; lean_object* v_entry_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___y_1076_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1065_ = lean_st_ref_get(v___y_1063_);
v_env_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1065_);
v_isExporting_1067_ = lean_ctor_get_uint8(v_env_1066_, sizeof(void*)*8);
lean_dec_ref(v_env_1066_);
v___x_1068_ = lean_st_ref_get(v___y_1063_);
v_env_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc_ref(v_env_1069_);
lean_dec(v___x_1068_);
v___x_1070_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2);
lean_inc(v_mod_1059_);
v_entry_1071_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1071_, 0, v_mod_1059_);
lean_ctor_set_uint8(v_entry_1071_, sizeof(void*)*1, v_isExporting_1067_);
lean_ctor_set_uint8(v_entry_1071_, sizeof(void*)*1 + 1, v_isMeta_1060_);
v___x_1072_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1073_ = lean_box(1);
v___x_1074_ = lean_box(0);
v___x_1101_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1070_, v___x_1072_, v_env_1069_, v___x_1073_, v___x_1074_);
v___x_1102_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v___x_1101_, v_entry_1071_);
if (v___x_1102_ == 0)
{
lean_object* v_cls_1103_; lean_object* v___x_1104_; lean_object* v_a_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___x_1125_; 
v_cls_1103_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4));
v___x_1104_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg(v_cls_1103_, v___y_1062_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1125_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
if (v___x_1125_ == 0)
{
lean_dec(v_hint_1061_);
lean_dec(v_mod_1059_);
v___y_1076_ = v___y_1063_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1126_; lean_object* v___y_1128_; 
v___x_1126_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11);
if (v_isExporting_1067_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16));
v___y_1128_ = v___x_1135_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17));
v___y_1128_ = v___x_1136_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = l_Lean_stringToMessageData(v___y_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1126_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
if (v_isMeta_1060_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14));
v___y_1112_ = v___x_1132_;
v___y_1113_ = v___x_1133_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15));
v___y_1112_ = v___x_1132_;
v___y_1113_ = v___x_1134_;
goto v___jp_1111_;
}
}
}
v___jp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___y_1107_);
lean_ctor_set(v___x_1109_, 1, v___y_1108_);
v___x_1110_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__4(v_cls_1103_, v___x_1109_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref(v___x_1110_);
v___y_1076_ = v___y_1063_;
goto v___jp_1075_;
}
else
{
lean_dec_ref(v_entry_1071_);
return v___x_1110_;
}
}
v___jp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1114_ = l_Lean_stringToMessageData(v___y_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___y_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_MessageData_ofName(v_mod_1059_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_Name_isAnonymous(v_hint_1061_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8);
v___x_1122_ = l_Lean_MessageData_ofName(v_hint_1061_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___y_1107_ = v___x_1119_;
v___y_1108_ = v___x_1123_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_hint_1061_);
v___x_1124_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9);
v___y_1107_ = v___x_1119_;
v___y_1108_ = v___x_1124_;
goto v___jp_1106_;
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_entry_1071_);
lean_dec(v_hint_1061_);
lean_dec(v_mod_1059_);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
v___jp_1075_:
{
lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_env_1079_; lean_object* v_nextMacroScope_1080_; lean_object* v_ngen_1081_; lean_object* v_auxDeclNGen_1082_; lean_object* v_traceState_1083_; lean_object* v_messages_1084_; lean_object* v_infoState_1085_; lean_object* v_snapshotTasks_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v___x_1077_ = lean_st_ref_take(v___y_1076_);
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_toEnvExtension_1078_);
v_env_1079_ = lean_ctor_get(v___x_1077_, 0);
v_nextMacroScope_1080_ = lean_ctor_get(v___x_1077_, 1);
v_ngen_1081_ = lean_ctor_get(v___x_1077_, 2);
v_auxDeclNGen_1082_ = lean_ctor_get(v___x_1077_, 3);
v_traceState_1083_ = lean_ctor_get(v___x_1077_, 4);
v_messages_1084_ = lean_ctor_get(v___x_1077_, 6);
v_infoState_1085_ = lean_ctor_get(v___x_1077_, 7);
v_snapshotTasks_1086_ = lean_ctor_get(v___x_1077_, 8);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1077_, 5);
lean_dec(v_unused_1100_);
v___x_1088_ = v___x_1077_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snapshotTasks_1086_);
lean_inc(v_infoState_1085_);
lean_inc(v_messages_1084_);
lean_inc(v_traceState_1083_);
lean_inc(v_auxDeclNGen_1082_);
lean_inc(v_ngen_1081_);
lean_inc(v_nextMacroScope_1080_);
lean_inc(v_env_1079_);
lean_dec(v___x_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_asyncMode_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_asyncMode_1090_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
lean_inc(v_asyncMode_1090_);
lean_dec_ref(v_toEnvExtension_1078_);
v___x_1091_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1072_, v_env_1079_, v_entry_1071_, v_asyncMode_1090_, v___x_1074_);
lean_dec(v_asyncMode_1090_);
v___x_1092_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 5, v___x_1092_);
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_nextMacroScope_1080_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_ngen_1081_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_auxDeclNGen_1082_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_traceState_1083_);
lean_ctor_set(v_reuseFailAlloc_1098_, 5, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 6, v_messages_1084_);
lean_ctor_set(v_reuseFailAlloc_1098_, 7, v_infoState_1085_);
lean_ctor_set(v_reuseFailAlloc_1098_, 8, v_snapshotTasks_1086_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_st_ref_set(v___y_1076_, v___x_1094_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_mod_1139_, lean_object* v_isMeta_1140_, lean_object* v_hint_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v_isMeta_boxed_1145_; lean_object* v_res_1146_; 
v_isMeta_boxed_1145_ = lean_unbox(v_isMeta_1140_);
v_res_1146_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_mod_1139_, v_isMeta_boxed_1145_, v_hint_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object* v_a_1147_, lean_object* v_x_1148_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
else
{
lean_object* v_key_1150_; lean_object* v_value_1151_; lean_object* v_tail_1152_; uint8_t v___x_1153_; 
v_key_1150_ = lean_ctor_get(v_x_1148_, 0);
v_value_1151_ = lean_ctor_get(v_x_1148_, 1);
v_tail_1152_ = lean_ctor_get(v_x_1148_, 2);
v___x_1153_ = lean_name_eq(v_key_1150_, v_a_1147_);
if (v___x_1153_ == 0)
{
v_x_1148_ = v_tail_1152_;
goto _start;
}
else
{
lean_object* v___x_1155_; 
lean_inc(v_value_1151_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_value_1151_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec(v_a_1156_);
return v_res_1158_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1159_; uint64_t v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(1723u);
v___x_1160_ = lean_uint64_of_nat(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_buckets_1163_; lean_object* v___x_1164_; uint64_t v___y_1166_; 
v_buckets_1163_ = lean_ctor_get(v_m_1161_, 1);
v___x_1164_ = lean_array_get_size(v_buckets_1163_);
if (lean_obj_tag(v_a_1162_) == 0)
{
uint64_t v___x_1180_; 
v___x_1180_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0);
v___y_1166_ = v___x_1180_;
goto v___jp_1165_;
}
else
{
uint64_t v_hash_1181_; 
v_hash_1181_ = lean_ctor_get_uint64(v_a_1162_, sizeof(void*)*2);
v___y_1166_ = v_hash_1181_;
goto v___jp_1165_;
}
v___jp_1165_:
{
uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v_fold_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1167_ = 32ULL;
v___x_1168_ = lean_uint64_shift_right(v___y_1166_, v___x_1167_);
v_fold_1169_ = lean_uint64_xor(v___y_1166_, v___x_1168_);
v___x_1170_ = 16ULL;
v___x_1171_ = lean_uint64_shift_right(v_fold_1169_, v___x_1170_);
v___x_1172_ = lean_uint64_xor(v_fold_1169_, v___x_1171_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = lean_usize_of_nat(v___x_1164_);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_usize_land(v___x_1173_, v___x_1176_);
v___x_1178_ = lean_array_uget_borrowed(v_buckets_1163_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_a_1162_, v___x_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_m_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_m_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(lean_object* v___x_1185_, lean_object* v_declName_1186_, lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_lt(v_i_1189_, v_sz_1188_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v_declName_1186_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1190_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v_modules_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v_toImport_1201_; lean_object* v_module_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1196_ = l_Lean_Environment_header(v___x_1185_);
v_modules_1197_ = lean_ctor_get(v___x_1196_, 3);
lean_inc_ref(v_modules_1197_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1199_ = lean_array_uget_borrowed(v_as_1187_, v_i_1189_);
v___x_1200_ = lean_array_get(v___x_1198_, v_modules_1197_, v_a_1199_);
lean_dec_ref(v_modules_1197_);
v_toImport_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_toImport_1201_);
lean_dec(v___x_1200_);
v_module_1202_ = lean_ctor_get(v_toImport_1201_, 0);
lean_inc(v_module_1202_);
lean_dec_ref(v_toImport_1201_);
v___x_1203_ = 0;
lean_inc(v_declName_1186_);
v___x_1204_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_1202_, v___x_1203_, v_declName_1186_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; 
lean_dec_ref(v___x_1204_);
v___x_1205_ = lean_box(0);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1189_, v___x_1206_);
v_i_1189_ = v___x_1207_;
v_b_1190_ = v___x_1205_;
goto _start;
}
else
{
lean_dec(v_declName_1186_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v___x_1209_, lean_object* v_declName_1210_, lean_object* v_as_1211_, lean_object* v_sz_1212_, lean_object* v_i_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
size_t v_sz_boxed_1218_; size_t v_i_boxed_1219_; lean_object* v_res_1220_; 
v_sz_boxed_1218_ = lean_unbox_usize(v_sz_1212_);
lean_dec(v_sz_1212_);
v_i_boxed_1219_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v___x_1209_, v_declName_1210_, v_as_1211_, v_sz_boxed_1218_, v_i_boxed_1219_, v_b_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v_as_1211_);
lean_dec_ref(v___x_1209_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1));
v___x_1224_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0));
v___x_1225_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(lean_object* v_declName_1228_, uint8_t v_isMeta_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v_env_1237_; lean_object* v___y_1239_; lean_object* v___x_1252_; 
v___x_1233_ = lean_st_ref_get(v___y_1231_);
v_env_1237_ = lean_ctor_get(v___x_1233_, 0);
lean_inc_ref(v_env_1237_);
lean_dec(v___x_1233_);
v___x_1252_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1237_, v_declName_1228_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref(v_env_1237_);
lean_dec(v_declName_1228_);
goto v___jp_1234_;
}
else
{
lean_object* v_val_1253_; lean_object* v___x_1254_; lean_object* v_modules_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = l_Lean_Environment_header(v_env_1237_);
v_modules_1255_ = lean_ctor_get(v___x_1254_, 3);
lean_inc_ref(v_modules_1255_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = lean_array_get_size(v_modules_1255_);
v___x_1257_ = lean_nat_dec_lt(v_val_1253_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_dec_ref(v_modules_1255_);
lean_dec(v_val_1253_);
lean_dec_ref(v_env_1237_);
lean_dec(v_declName_1228_);
goto v___jp_1234_;
}
else
{
lean_object* v___x_1258_; lean_object* v_env_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___y_1263_; 
v___x_1258_ = lean_st_ref_get(v___y_1231_);
v_env_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_env_1259_);
lean_dec(v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2);
v___x_1261_ = lean_array_fget(v_modules_1255_, v_val_1253_);
lean_dec(v_val_1253_);
lean_dec_ref(v_modules_1255_);
if (v_isMeta_1229_ == 0)
{
lean_dec_ref(v_env_1259_);
v___y_1263_ = v_isMeta_1229_;
goto v___jp_1262_;
}
else
{
uint8_t v___x_1274_; 
lean_inc(v_declName_1228_);
v___x_1274_ = l_Lean_isMarkedMeta(v_env_1259_, v_declName_1228_);
if (v___x_1274_ == 0)
{
v___y_1263_ = v_isMeta_1229_;
goto v___jp_1262_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = 0;
v___y_1263_ = v___x_1275_;
goto v___jp_1262_;
}
}
v___jp_1262_:
{
lean_object* v_toImport_1264_; lean_object* v_module_1265_; lean_object* v___x_1266_; 
v_toImport_1264_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref(v_toImport_1264_);
lean_dec(v___x_1261_);
v_module_1265_ = lean_ctor_get(v_toImport_1264_, 0);
lean_inc(v_module_1265_);
lean_dec_ref(v_toImport_1264_);
lean_inc(v_declName_1228_);
v___x_1266_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_1265_, v___y_1263_, v_declName_1228_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v___x_1266_);
v___x_1267_ = l_Lean_indirectModUseExt;
v___x_1268_ = lean_box(1);
v___x_1269_ = lean_box(0);
lean_inc_ref(v_env_1237_);
v___x_1270_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1260_, v___x_1267_, v_env_1237_, v___x_1268_, v___x_1269_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v___x_1270_, v_declName_1228_);
lean_dec(v___x_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3));
v___y_1239_ = v___x_1272_;
goto v___jp_1238_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1273_);
lean_dec_ref(v___x_1271_);
v___y_1239_ = v_val_1273_;
goto v___jp_1238_;
}
}
else
{
lean_dec_ref(v_env_1237_);
lean_dec(v_declName_1228_);
return v___x_1266_;
}
}
}
}
v___jp_1234_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = lean_box(0);
v_sz_1241_ = lean_array_size(v___y_1239_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v_env_1237_, v_declName_1228_, v___y_1239_, v_sz_1241_, v___x_1242_, v___x_1240_, v___y_1230_, v___y_1231_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v_env_1237_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1243_, 0);
lean_dec(v_unused_1251_);
v___x_1245_ = v___x_1243_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v___x_1243_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1240_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1240_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1276_, lean_object* v_isMeta_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_isMeta_boxed_1281_; lean_object* v_res_1282_; 
v_isMeta_boxed_1281_ = lean_unbox(v_isMeta_1277_);
v_res_1282_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v_declName_1276_, v_isMeta_boxed_1281_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(uint8_t v___y_1283_, lean_object* v_as_1284_, size_t v_i_1285_, size_t v_stop_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_eq(v_i_1285_, v_stop_1286_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_array_uget_borrowed(v_as_1284_, v_i_1285_);
lean_inc(v___x_1292_);
v___x_1293_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v___x_1292_, v___y_1283_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; size_t v___x_1295_; size_t v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1285_, v___x_1295_);
v_i_1285_ = v___x_1296_;
v_b_1287_ = v_a_1294_;
goto _start;
}
else
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_b_1287_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2___boxed(lean_object* v___y_1299_, lean_object* v_as_1300_, lean_object* v_i_1301_, lean_object* v_stop_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v___y_6893__boxed_1307_; size_t v_i_boxed_1308_; size_t v_stop_boxed_1309_; lean_object* v_res_1310_; 
v___y_6893__boxed_1307_ = lean_unbox(v___y_1299_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_stop_boxed_1309_ = lean_unbox_usize(v_stop_1302_);
lean_dec(v_stop_1302_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_6893__boxed_1307_, v_as_1300_, v_i_boxed_1308_, v_stop_boxed_1309_, v_b_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_as_1300_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_bs_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_usize_dec_lt(v_i_1312_, v_sz_1311_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_bs_1313_);
return v___x_1318_;
}
else
{
lean_object* v_v_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_v_1319_ = lean_array_uget_borrowed(v_bs_1313_, v_i_1312_);
v___x_1320_ = lean_box(0);
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v_v_1319_);
v___x_1321_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_1319_, v___x_1320_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v_bs_x27_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v_bs_x27_1324_ = lean_array_uset(v_bs_1313_, v_i_1312_, v___x_1323_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1312_, v___x_1325_);
v___x_1327_ = lean_array_uset(v_bs_x27_1324_, v_i_1312_, v_a_1322_);
v_i_1312_ = v___x_1326_;
v_bs_1313_ = v___x_1327_;
goto _start;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v_bs_1313_);
v_a_1329_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1321_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1321_);
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
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0___boxed(lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_bs_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_boxed_1343_, v_i_boxed_1344_, v_bs_1339_, v___y_1340_, v___y_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, lean_object* v___x_1349_, lean_object* v___x_1350_, lean_object* v_decl_1351_, lean_object* v_stx_1352_, uint8_t v_kind_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; size_t v___y_1422_; uint8_t v___y_1423_; uint8_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = 0;
v___x_1473_ = l_Lean_instBEqAttributeKind_beq(v_kind_1353_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec(v_stx_1352_);
lean_dec(v_decl_1351_);
lean_dec_ref(v___x_1350_);
lean_dec_ref(v___x_1349_);
lean_dec(v___x_1346_);
v___x_1474_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_1348_, v_kind_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v___x_1474_;
}
else
{
goto v___jp_1432_;
}
v___jp_1357_:
{
lean_object* v___x_1361_; lean_object* v_env_1362_; lean_object* v_options_1363_; lean_object* v_ref_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1361_ = lean_st_ref_get(v___y_1360_);
v_env_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_env_1362_);
lean_dec(v___x_1361_);
v_options_1363_ = lean_ctor_get(v___y_1358_, 2);
lean_inc_ref(v_options_1363_);
v_ref_1364_ = lean_ctor_get(v___y_1358_, 5);
lean_inc(v_ref_1364_);
lean_dec_ref(v___y_1358_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_env_1362_);
lean_ctor_set(v___x_1365_, 1, v_options_1363_);
lean_inc(v_decl_1351_);
v___x_1366_ = l_Lean_CodeAction_mkCommandCodeAction(v_decl_1351_, v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_ref_1364_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1400_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1400_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v_env_1372_; lean_object* v_nextMacroScope_1373_; lean_object* v_ngen_1374_; lean_object* v_auxDeclNGen_1375_; lean_object* v_traceState_1376_; lean_object* v_messages_1377_; lean_object* v_infoState_1378_; lean_object* v_snapshotTasks_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1398_; 
v___x_1371_ = lean_st_ref_take(v___y_1360_);
v_env_1372_ = lean_ctor_get(v___x_1371_, 0);
v_nextMacroScope_1373_ = lean_ctor_get(v___x_1371_, 1);
v_ngen_1374_ = lean_ctor_get(v___x_1371_, 2);
v_auxDeclNGen_1375_ = lean_ctor_get(v___x_1371_, 3);
v_traceState_1376_ = lean_ctor_get(v___x_1371_, 4);
v_messages_1377_ = lean_ctor_get(v___x_1371_, 6);
v_infoState_1378_ = lean_ctor_get(v___x_1371_, 7);
v_snapshotTasks_1379_ = lean_ctor_get(v___x_1371_, 8);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1371_, 5);
lean_dec(v_unused_1399_);
v___x_1381_ = v___x_1371_;
v_isShared_1382_ = v_isSharedCheck_1398_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snapshotTasks_1379_);
lean_inc(v_infoState_1378_);
lean_inc(v_messages_1377_);
lean_inc(v_traceState_1376_);
lean_inc(v_auxDeclNGen_1375_);
lean_inc(v_ngen_1374_);
lean_inc(v_nextMacroScope_1373_);
lean_inc(v_env_1372_);
lean_dec(v___x_1371_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1398_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v_toEnvExtension_1384_; lean_object* v_asyncMode_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1383_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_toEnvExtension_1384_);
v_asyncMode_1385_ = lean_ctor_get(v_toEnvExtension_1384_, 2);
lean_inc(v_asyncMode_1385_);
lean_dec_ref(v_toEnvExtension_1384_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_decl_1351_);
lean_ctor_set(v___x_1386_, 1, v___y_1359_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1367_);
v___x_1388_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1383_, v_env_1372_, v___x_1387_, v_asyncMode_1385_, v___x_1346_);
lean_dec(v_asyncMode_1385_);
v___x_1389_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 5, v___x_1389_);
lean_ctor_set(v___x_1381_, 0, v___x_1388_);
v___x_1391_ = v___x_1381_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_nextMacroScope_1373_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_ngen_1374_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_auxDeclNGen_1375_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_traceState_1376_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_messages_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_infoState_1378_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v_snapshotTasks_1379_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_st_ref_set(v___y_1360_, v___x_1391_);
lean_dec(v___y_1360_);
v___x_1393_ = lean_box(0);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1393_);
v___x_1395_ = v___x_1369_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_decl_1351_);
lean_dec(v___x_1346_);
v_a_1401_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1403_ = v___x_1366_;
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1366_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1405_ = lean_io_error_to_string(v_a_1401_);
v___x_1406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
v___x_1407_ = l_Lean_MessageData_ofFormat(v___x_1406_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_ref_1364_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1408_);
v___x_1410_ = v___x_1403_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
v___jp_1413_:
{
if (lean_obj_tag(v___y_1417_) == 0)
{
lean_dec_ref(v___y_1417_);
v___y_1358_ = v___y_1414_;
v___y_1359_ = v___y_1415_;
v___y_1360_ = v___y_1416_;
goto v___jp_1357_;
}
else
{
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_decl_1351_);
lean_dec(v___x_1346_);
return v___y_1417_;
}
}
v___jp_1418_:
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = lean_array_get_size(v___y_1420_);
v___x_1425_ = lean_nat_dec_lt(v___x_1347_, v___x_1424_);
if (v___x_1425_ == 0)
{
v___y_1358_ = v___y_1419_;
v___y_1359_ = v___y_1420_;
v___y_1360_ = v___y_1421_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
if (v___x_1427_ == 0)
{
if (v___x_1425_ == 0)
{
v___y_1358_ = v___y_1419_;
v___y_1359_ = v___y_1420_;
v___y_1360_ = v___y_1421_;
goto v___jp_1357_;
}
else
{
size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_usize_of_nat(v___x_1424_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_1423_, v___y_1420_, v___y_1422_, v___x_1428_, v___x_1426_, v___y_1419_, v___y_1421_);
v___y_1414_ = v___y_1419_;
v___y_1415_ = v___y_1420_;
v___y_1416_ = v___y_1421_;
v___y_1417_ = v___x_1429_;
goto v___jp_1413_;
}
}
else
{
size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_usize_of_nat(v___x_1424_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_1423_, v___y_1420_, v___y_1422_, v___x_1430_, v___x_1426_, v___y_1419_, v___y_1421_);
v___y_1414_ = v___y_1419_;
v___y_1415_ = v___y_1420_;
v___y_1416_ = v___y_1421_;
v___y_1417_ = v___x_1431_;
goto v___jp_1413_;
}
}
}
v___jp_1432_:
{
lean_object* v___x_1433_; 
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v_decl_1351_);
v___x_1433_ = l_Lean_ensureAttrDeclIsMeta(v___x_1348_, v_decl_1351_, v_kind_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1471_);
v___x_1435_ = v___x_1433_;
v_isShared_1436_ = v_isSharedCheck_1470_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v___x_1433_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1470_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = l_Lean_Name_mkStr2(v___x_1349_, v___x_1350_);
lean_inc(v_stx_1352_);
v___x_1438_ = l_Lean_Syntax_isOfKind(v_stx_1352_, v___x_1437_);
lean_dec(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_stx_1352_);
lean_dec(v_decl_1351_);
lean_dec(v___x_1346_);
v___x_1439_ = lean_box(0);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1439_);
v___x_1441_ = v___x_1435_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; size_t v_sz_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
lean_del_object(v___x_1435_);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1443_);
lean_dec(v_stx_1352_);
v___x_1445_ = l_Lean_Syntax_getArgs(v___x_1444_);
lean_dec(v___x_1444_);
v_sz_1446_ = lean_array_size(v___x_1445_);
v___x_1447_ = ((size_t)0ULL);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_1446_, v___x_1447_, v___x_1445_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1461_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_env_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_st_ref_get(v___y_1355_);
v_env_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc_ref(v_env_1454_);
lean_dec(v___x_1453_);
lean_inc(v_decl_1351_);
v___x_1455_ = lean_decl_get_sorry_dep(v_env_1454_, v_decl_1351_);
if (lean_obj_tag(v___x_1455_) == 0)
{
uint8_t v___x_1456_; 
lean_del_object(v___x_1451_);
v___x_1456_ = 0;
v___y_1419_ = v___y_1354_;
v___y_1420_ = v_a_1449_;
v___y_1421_ = v___y_1355_;
v___y_1422_ = v___x_1447_;
v___y_1423_ = v___x_1456_;
goto v___jp_1418_;
}
else
{
lean_dec_ref(v___x_1455_);
if (v___x_1438_ == 0)
{
lean_del_object(v___x_1451_);
v___y_1419_ = v___y_1354_;
v___y_1420_ = v_a_1449_;
v___y_1421_ = v___y_1355_;
v___y_1422_ = v___x_1447_;
v___y_1423_ = v___x_1438_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec(v_a_1449_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_decl_1351_);
lean_dec(v___x_1346_);
v___x_1457_ = lean_box(0);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1457_);
v___x_1459_ = v___x_1451_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
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
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_decl_1351_);
lean_dec(v___x_1346_);
v_a_1462_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1448_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1448_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
else
{
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_stx_1352_);
lean_dec(v_decl_1351_);
lean_dec_ref(v___x_1350_);
lean_dec_ref(v___x_1349_);
lean_dec(v___x_1346_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v_decl_1480_, lean_object* v_stx_1481_, lean_object* v_kind_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v_kind_boxed_1486_; lean_object* v_res_1487_; 
v_kind_boxed_1486_ = lean_unbox(v_kind_1482_);
v_res_1487_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_1475_, v___x_1476_, v___x_1477_, v___x_1478_, v___x_1479_, v_decl_1480_, v_stx_1481_, v_kind_boxed_1486_, v___y_1483_, v___y_1484_);
lean_dec(v___x_1476_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(lean_object* v___x_1488_, lean_object* v_decl_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1493_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_1494_ = l_Lean_MessageData_ofName(v___x_1488_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_1497_, v___y_1490_, v___y_1491_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object* v___x_1499_, lean_object* v_decl_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_1499_, v_decl_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_decl_1500_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_));
v___x_1540_ = l_Lean_registerBuiltinAttribute(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(lean_object* v_cls_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___redArg(v_cls_1543_, v___y_1544_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___boxed(lean_object* v_cls_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(v_cls_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_1554_, v_a_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_m_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b2_1557_, v_m_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_m_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_1562_, v_x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_1565_, v_x_1566_, v_x_1567_);
lean_dec_ref(v_x_1567_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1570_, lean_object* v_a_1571_, lean_object* v_x_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_a_1571_, v_x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1574_, lean_object* v_a_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__7(v_00_u03b2_1574_, v_a_1575_, v_x_1576_);
lean_dec(v_x_1576_);
lean_dec(v_a_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1578_, lean_object* v_x_1579_, size_t v_x_1580_, lean_object* v_x_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_1579_, v_x_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
size_t v_x_7428__boxed_1587_; uint8_t v_res_1588_; lean_object* v_r_1589_; 
v_x_7428__boxed_1587_ = lean_unbox_usize(v_x_1585_);
lean_dec(v_x_1585_);
v_res_1588_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1583_, v_x_1584_, v_x_7428__boxed_1587_, v_x_1586_);
lean_dec_ref(v_x_1586_);
v_r_1589_ = lean_box(v_res_1588_);
return v_r_1589_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1590_, lean_object* v_keys_1591_, lean_object* v_vals_1592_, lean_object* v_heq_1593_, lean_object* v_i_1594_, lean_object* v_k_1595_){
_start:
{
uint8_t v___x_1596_; 
v___x_1596_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___redArg(v_keys_1591_, v_i_1594_, v_k_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1597_, lean_object* v_keys_1598_, lean_object* v_vals_1599_, lean_object* v_heq_1600_, lean_object* v_i_1601_, lean_object* v_k_1602_){
_start:
{
uint8_t v_res_1603_; lean_object* v_r_1604_; 
v_res_1603_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_1597_, v_keys_1598_, v_vals_1599_, v_heq_1600_, v_i_1601_, v_k_1602_);
lean_dec_ref(v_k_1602_);
lean_dec_ref(v_vals_1599_);
lean_dec_ref(v_keys_1598_);
v_r_1604_ = lean_box(v_res_1603_);
return v_r_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(lean_object* v_nilFn_1605_, lean_object* v_consFn_1606_, lean_object* v_x_1607_){
_start:
{
if (lean_obj_tag(v_x_1607_) == 0)
{
lean_dec_ref(v_consFn_1606_);
lean_inc_ref(v_nilFn_1605_);
return v_nilFn_1605_;
}
else
{
lean_object* v_head_1608_; lean_object* v_tail_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_head_1608_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_head_1608_);
v_tail_1609_ = lean_ctor_get(v_x_1607_, 1);
lean_inc(v_tail_1609_);
lean_dec_ref(v_x_1607_);
v___x_1610_ = l_Lean_instToExprName___private__1(v_head_1608_);
lean_inc_ref(v_consFn_1606_);
v___x_1611_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_1605_, v_consFn_1606_, v_tail_1609_);
v___x_1612_ = l_Lean_mkAppB(v_consFn_1606_, v___x_1610_, v___x_1611_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0___boxed(lean_object* v_nilFn_1613_, lean_object* v_consFn_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_1613_, v_consFn_1614_, v_x_1615_);
lean_dec_ref(v_nilFn_1613_);
return v_res_1616_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1));
v___x_1624_ = l_Lean_mkConst(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v_type_1631_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4));
v_type_1631_ = l_Lean_mkConst(v___x_1630_, v___x_1629_);
return v_type_1631_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9));
v___x_1641_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8));
v___x_1642_ = l_Lean_mkConst(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1644_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
lean_ctor_set(v___x_1644_, 2, v___x_1643_);
lean_ctor_set(v___x_1644_, 3, v___x_1643_);
lean_ctor_set(v___x_1644_, 4, v___x_1643_);
lean_ctor_set(v___x_1644_, 5, v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(32u);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13(void){
_start:
{
size_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1648_ = ((size_t)5ULL);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_unsigned_to_nat(32u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12);
v___x_1653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
lean_ctor_set(v___x_1653_, 2, v___x_1649_);
lean_ctor_set(v___x_1653_, 3, v___x_1649_);
lean_ctor_set_usize(v___x_1653_, 4, v___x_1648_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
lean_ctor_set(v___x_1655_, 3, v___x_1654_);
lean_ctor_set(v___x_1655_, 4, v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1656_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14);
v___x_1657_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13);
v___x_1658_ = lean_box(1);
v___x_1659_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11);
v___x_1660_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1659_);
lean_ctor_set(v___x_1661_, 2, v___x_1658_);
lean_ctor_set(v___x_1661_, 3, v___x_1657_);
lean_ctor_set(v___x_1661_, 4, v___x_1656_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9));
v___x_1670_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19));
v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21(void){
_start:
{
lean_object* v_type_1672_; lean_object* v___x_1673_; lean_object* v_nil_1674_; 
v_type_1672_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5);
v___x_1673_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20);
v_nil_1674_ = l_Lean_Expr_app___override(v___x_1673_, v_type_1672_);
return v_nil_1674_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9));
v___x_1680_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23));
v___x_1681_ = l_Lean_mkConst(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25(void){
_start:
{
lean_object* v_type_1682_; lean_object* v___x_1683_; lean_object* v_cons_1684_; 
v_type_1682_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5);
v___x_1683_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24);
v_cons_1684_ = l_Lean_Expr_app___override(v___x_1683_, v_type_1682_);
return v_cons_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(lean_object* v_declName_1685_, lean_object* v_args_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_type_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2);
v_type_1692_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5);
v___x_1693_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10);
v___x_1694_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15);
v___x_1695_ = lean_st_mk_ref(v___x_1694_);
lean_inc(v_declName_1685_);
v___x_1696_ = l_Lean_mkConst(v_declName_1685_, v___x_1690_);
v___x_1697_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17));
v___x_1698_ = l_Lean_Name_append(v_declName_1685_, v___x_1697_);
lean_inc(v_a_1688_);
lean_inc_ref(v_a_1687_);
v___x_1699_ = l_Lean_Core_mkFreshUserName(v___x_1698_, v_a_1687_, v_a_1688_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v_nil_1701_; lean_object* v_cons_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_val_1710_; lean_object* v___x_1711_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v_nil_1701_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21);
v_cons_1702_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25);
v___x_1703_ = lean_array_to_list(v_args_1686_);
v___x_1704_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nil_1701_, v_cons_1702_, v___x_1703_);
v___x_1705_ = l_Lean_mkAppB(v___x_1693_, v_type_1692_, v___x_1704_);
v___x_1706_ = lean_unsigned_to_nat(2u);
v___x_1707_ = lean_mk_empty_array_with_capacity(v___x_1706_);
v___x_1708_ = lean_array_push(v___x_1707_, v___x_1705_);
v___x_1709_ = lean_array_push(v___x_1708_, v___x_1696_);
v_val_1710_ = l_Lean_mkAppN(v___x_1691_, v___x_1709_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = l_Lean_declareBuiltin(v_a_1700_, v_val_1710_, v_a_1687_, v_a_1688_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_st_ref_get(v___x_1695_);
lean_dec(v___x_1695_);
lean_dec(v___x_1716_);
if (v_isShared_1715_ == 0)
{
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_dec(v___x_1695_);
return v___x_1711_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___x_1696_);
lean_dec(v___x_1695_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec_ref(v_args_1686_);
v_a_1721_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1699_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1699_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___boxed(lean_object* v_declName_1729_, lean_object* v_args_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(v_declName_1729_, v_args_1730_, v_a_1731_, v_a_1732_);
return v_res_1734_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_));
v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v_decl_1740_, lean_object* v_stx_1741_, uint8_t v_kind_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = 0;
v___x_1780_ = l_Lean_instBEqAttributeKind_beq(v_kind_1742_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_stx_1741_);
lean_dec(v_decl_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v___x_1738_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_));
v___x_1782_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_1781_, v_kind_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v___x_1782_;
}
else
{
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = l_Lean_Name_mkStr2(v___x_1738_, v___x_1739_);
lean_inc(v_stx_1741_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_stx_1741_, v___x_1747_);
lean_dec(v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_stx_1741_);
lean_dec(v_decl_1740_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_);
v___x_1750_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_1749_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_args_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = l_Lean_Syntax_getArg(v_stx_1741_, v___x_1751_);
lean_dec(v_stx_1741_);
v_args_1753_ = l_Lean_Syntax_getArgs(v___x_1752_);
lean_dec(v___x_1752_);
v_sz_1754_ = lean_array_size(v_args_1753_);
v___x_1755_ = ((size_t)0ULL);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_1754_, v___x_1755_, v_args_1753_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1770_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1770_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1770_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v_env_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_st_ref_get(v___y_1744_);
v_env_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc_ref(v_env_1762_);
lean_dec(v___x_1761_);
lean_inc(v_decl_1740_);
v___x_1763_ = lean_decl_get_sorry_dep(v_env_1762_, v_decl_1740_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1764_; 
lean_del_object(v___x_1759_);
v___x_1764_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(v_decl_1740_, v_a_1757_, v___y_1743_, v___y_1744_);
return v___x_1764_;
}
else
{
lean_dec_ref(v___x_1763_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1759_);
v___x_1765_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(v_decl_1740_, v_a_1757_, v___y_1743_, v___y_1744_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v_a_1757_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v_decl_1740_);
v___x_1766_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1766_);
v___x_1768_ = v___x_1759_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v_decl_1740_);
v_a_1771_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1756_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1756_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v_decl_1785_, lean_object* v_stx_1786_, lean_object* v_kind_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v_kind_boxed_1791_; lean_object* v_res_1792_; 
v_kind_boxed_1791_ = lean_unbox(v_kind_1787_);
v_res_1792_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(v___x_1783_, v___x_1784_, v_decl_1785_, v_stx_1786_, v_kind_boxed_1791_, v___y_1788_, v___y_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_));
v___x_1825_ = l_Lean_registerBuiltinAttribute(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
return v_res_1827_;
}
}
lean_object* runtime_initialize_Lean_Server_CodeActions_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_CodeAction_holeCodeActionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_CodeAction_holeCodeActionExt);
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_CodeAction_builtinCmdCodeActions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_CodeAction_builtinCmdCodeActions);
lean_dec_ref(res);
res = l_Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_CodeAction_cmdCodeActionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionExt);
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_CodeActions_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
