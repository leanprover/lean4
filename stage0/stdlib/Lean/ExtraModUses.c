// Lean compiler output
// Module: Lean.ExtraModUses
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr import Init.Data.Range.Polymorphic.Stream
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqIndirectModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqIndirectModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqIndirectModUse___closed__0 = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqIndirectModUse = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "indirectModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 173, 36, 115, 222, 236, 117, 108)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_indirectModUseExt;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__0;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "recording indirect mod use of `"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "` ("};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__3;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__4 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqExtraModUse___closed__0 = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqExtraModUse = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableExtraModUse___closed__0 = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableExtraModUse = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isExported"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprExtraModUse_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprExtraModUse___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprExtraModUse = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object*);
static const lean_array_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ExtraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 69, 125, 143, 117, 200, 37, 103)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 125, 98, 145, 27, 242, 139, 173)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 80, 45, 80, 85, 236, 79, 117)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 241, 212, 4, 163, 62, 5, 148)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
static lean_once_cell_t l_Lean_getExtraModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__0;
static lean_once_cell_t l_Lean_getExtraModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__4_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__10_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__11_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__12_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object**);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___redArg___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___redArg___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___redArg___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isExtraRevModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 81, 220, 33, 30, 172, 4, 212)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
static const lean_ctor_object l_Lean_isExtraRevModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isExtraRevModUse___closed__0 = (const lean_object*)&l_Lean_isExtraRevModUse___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "recording extra reverse use of current module"};
static const lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 211, 254, 26, 237, 216, 211, 30)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 203, 147, 114, 124, 159, 234, 194)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 198, 100, 78, 72, 145, 180, 196)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 81, 65, 191, 6, 222, 76)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object*);
uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_kind_3_; lean_object* v_declName_4_; lean_object* v_kind_5_; lean_object* v_declName_6_; uint8_t v___x_7_; 
v_kind_3_ = lean_ctor_get(v_x_1_, 0);
v_declName_4_ = lean_ctor_get(v_x_1_, 1);
v_kind_5_ = lean_ctor_get(v_x_2_, 0);
v_declName_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_string_dec_eq(v_kind_3_, v_kind_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_name_eq(v_declName_4_, v_declName_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT void l_Lean_instBEqIndirectModUse_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_Lean_instBEqIndirectModUse_beq(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lean_instBEqIndirectModUse_beq(v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_array_mk(v_es_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_s_18_, lean_object* v_x_19_){
_start:
{
lean_inc_ref(v_s_18_);
return v_s_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_s_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_s_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec_ref(v_s_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
return v_x_23_;
}
else
{
lean_object* v_key_25_; lean_object* v_value_26_; lean_object* v_tail_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_53_; 
v_key_25_ = lean_ctor_get(v_x_24_, 0);
v_value_26_ = lean_ctor_get(v_x_24_, 1);
v_tail_27_ = lean_ctor_get(v_x_24_, 2);
v_isSharedCheck_53_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_53_ == 0)
{
v___x_29_ = v_x_24_;
v_isShared_30_ = v_isSharedCheck_53_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_tail_27_);
lean_inc(v_value_26_);
lean_inc(v_key_25_);
lean_dec(v_x_24_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_53_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; uint64_t v___y_33_; 
v___x_31_ = lean_array_get_size(v_x_23_);
if (lean_obj_tag(v_key_25_) == 0)
{
uint64_t v___x_51_; 
v___x_51_ = 1723ULL;
v___y_33_ = v___x_51_;
goto v___jp_32_;
}
else
{
uint64_t v_hash_52_; 
v_hash_52_ = lean_ctor_get_uint64(v_key_25_, sizeof(void*)*2);
v___y_33_ = v_hash_52_;
goto v___jp_32_;
}
v___jp_32_:
{
uint64_t v___x_34_; uint64_t v___x_35_; uint64_t v_fold_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_34_ = 32ULL;
v___x_35_ = lean_uint64_shift_right(v___y_33_, v___x_34_);
v_fold_36_ = lean_uint64_xor(v___y_33_, v___x_35_);
v___x_37_ = 16ULL;
v___x_38_ = lean_uint64_shift_right(v_fold_36_, v___x_37_);
v___x_39_ = lean_uint64_xor(v_fold_36_, v___x_38_);
v___x_40_ = lean_uint64_to_usize(v___x_39_);
v___x_41_ = lean_usize_of_nat(v___x_31_);
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_sub(v___x_41_, v___x_42_);
v___x_44_ = lean_usize_land(v___x_40_, v___x_43_);
v___x_45_ = lean_array_uget_borrowed(v_x_23_, v___x_44_);
lean_inc(v___x_45_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___x_45_);
v___x_47_ = v___x_29_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_key_25_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_value_26_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v___x_45_);
v___x_47_ = v_reuseFailAlloc_50_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = lean_array_uset(v_x_23_, v___x_44_, v___x_47_);
v_x_23_ = v___x_48_;
v_x_24_ = v_tail_27_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_54_, lean_object* v_source_55_, lean_object* v_target_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_get_size(v_source_55_);
v___x_58_ = lean_nat_dec_lt(v_i_54_, v___x_57_);
if (v___x_58_ == 0)
{
lean_dec_ref(v_source_55_);
lean_dec(v_i_54_);
return v_target_56_;
}
else
{
lean_object* v_es_59_; lean_object* v___x_60_; lean_object* v_source_61_; lean_object* v_target_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_es_59_ = lean_array_fget(v_source_55_, v_i_54_);
v___x_60_ = lean_box(0);
v_source_61_ = lean_array_fset(v_source_55_, v_i_54_, v___x_60_);
v_target_62_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_56_, v_es_59_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_i_54_, v___x_63_);
lean_dec(v_i_54_);
v_i_54_ = v___x_64_;
v_source_55_ = v_source_61_;
v_target_56_ = v_target_62_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_nbuckets_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_67_ = lean_array_get_size(v_data_66_);
v___x_68_ = lean_unsigned_to_nat(2u);
v_nbuckets_69_ = lean_nat_mul(v___x_67_, v___x_68_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_box(0);
v___x_72_ = lean_mk_array(v_nbuckets_69_, v___x_71_);
v___x_73_ = lean_array_propagate_mark(v_data_66_, v___x_72_);
v___x_74_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_70_, v_data_66_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___y_80_; 
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_80_ = v___x_83_;
goto v___jp_79_;
}
else
{
lean_object* v_val_84_; 
v_val_84_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_x_78_, 1);
v___y_80_ = v_val_84_;
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_array_push(v___y_80_, v_val_77_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_85_, lean_object* v_a_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_val_90_; lean_object* v___x_91_; 
v___x_88_ = lean_box(0);
v___x_89_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_85_, v___x_88_);
v_val_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_val_90_);
lean_dec(v___x_89_);
v___x_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_91_, 0, v_a_86_);
lean_ctor_set(v___x_91_, 1, v_val_90_);
lean_ctor_set(v___x_91_, 2, v_x_87_);
return v___x_91_;
}
else
{
lean_object* v_key_92_; lean_object* v_value_93_; lean_object* v_tail_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_109_; 
v_key_92_ = lean_ctor_get(v_x_87_, 0);
v_value_93_ = lean_ctor_get(v_x_87_, 1);
v_tail_94_ = lean_ctor_get(v_x_87_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_109_ == 0)
{
v___x_96_ = v_x_87_;
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_tail_94_);
lean_inc(v_value_93_);
lean_inc(v_key_92_);
lean_dec(v_x_87_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = lean_name_eq(v_key_92_, v_a_86_);
if (v___x_98_ == 0)
{
lean_object* v_tail_99_; lean_object* v___x_101_; 
v_tail_99_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_85_, v_a_86_, v_tail_94_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_tail_99_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_key_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_value_93_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_tail_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_val_105_; lean_object* v___x_107_; 
lean_dec(v_key_92_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_value_93_);
v___x_104_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_85_, v___x_103_);
v_val_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_105_);
lean_dec(v___x_104_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_val_105_);
lean_ctor_set(v___x_96_, 0, v_a_86_);
v___x_107_ = v___x_96_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_86_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_val_105_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_tail_94_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
else
{
lean_object* v_key_113_; lean_object* v_tail_114_; uint8_t v___x_115_; 
v_key_113_ = lean_ctor_get(v_x_111_, 0);
v_tail_114_ = lean_ctor_get(v_x_111_, 2);
v___x_115_ = lean_name_eq(v_key_113_, v_a_110_);
if (v___x_115_ == 0)
{
v_x_111_ = v_tail_114_;
goto _start;
}
else
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_110_ = stack[0].m_obj;
lean_object* v_x_111_ = stack[1].m_obj;
uint8_t v_res_117_;
v_res_117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_110_, v_x_111_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec(v_a_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_122_, lean_object* v_m_123_, lean_object* v_a_124_){
_start:
{
size_t v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v_size_132_; lean_object* v_buckets_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_180_; 
v_size_132_ = lean_ctor_get(v_m_123_, 0);
v_buckets_133_ = lean_ctor_get(v_m_123_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_m_123_);
if (v_isSharedCheck_180_ == 0)
{
v___x_135_ = v_m_123_;
v_isShared_136_ = v_isSharedCheck_180_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_buckets_133_);
lean_inc(v_size_132_);
lean_dec(v_m_123_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_180_;
goto v_resetjp_134_;
}
v___jp_125_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_array_uset(v___y_127_, v___y_126_, v___y_128_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___y_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___y_139_; 
v___x_137_ = lean_array_get_size(v_buckets_133_);
if (lean_obj_tag(v_a_124_) == 0)
{
uint64_t v___x_178_; 
v___x_178_ = 1723ULL;
v___y_139_ = v___x_178_;
goto v___jp_138_;
}
else
{
uint64_t v_hash_179_; 
v_hash_179_ = lean_ctor_get_uint64(v_a_124_, sizeof(void*)*2);
v___y_139_ = v_hash_179_;
goto v___jp_138_;
}
v___jp_138_:
{
uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v_fold_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v_bkt_151_; uint8_t v___x_152_; 
v___x_140_ = 32ULL;
v___x_141_ = lean_uint64_shift_right(v___y_139_, v___x_140_);
v_fold_142_ = lean_uint64_xor(v___y_139_, v___x_141_);
v___x_143_ = 16ULL;
v___x_144_ = lean_uint64_shift_right(v_fold_142_, v___x_143_);
v___x_145_ = lean_uint64_xor(v_fold_142_, v___x_144_);
v___x_146_ = lean_uint64_to_usize(v___x_145_);
v___x_147_ = lean_usize_of_nat(v___x_137_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_sub(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_land(v___x_146_, v___x_149_);
v_bkt_151_ = lean_array_uget_borrowed(v_buckets_133_, v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_124_, v_bkt_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_size_x27_156_; lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_153_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___x_154_ = lean_array_push(v___x_153_, v_val_122_);
v___x_155_ = lean_unsigned_to_nat(1u);
v_size_x27_156_ = lean_nat_add(v_size_132_, v___x_155_);
lean_dec(v_size_132_);
lean_inc(v_bkt_151_);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v_a_124_);
lean_ctor_set(v___x_157_, 1, v___x_154_);
lean_ctor_set(v___x_157_, 2, v_bkt_151_);
v_buckets_x27_158_ = lean_array_uset(v_buckets_133_, v___x_150_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = lean_nat_mul(v_size_x27_156_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_div(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_array_get_size(v_buckets_x27_158_);
v___x_164_ = lean_nat_dec_le(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v_val_165_; lean_object* v___x_167_; 
v_val_165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_158_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_165_);
lean_ctor_set(v___x_135_, 0, v_size_x27_156_);
v___x_167_ = v___x_135_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_val_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_158_);
lean_ctor_set(v___x_135_, 0, v_size_x27_156_);
v___x_170_ = v___x_135_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_buckets_x27_158_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v___x_172_; lean_object* v_buckets_x27_173_; lean_object* v_bkt_x27_174_; uint8_t v___x_175_; 
lean_inc(v_bkt_151_);
lean_del_object(v___x_135_);
v___x_172_ = lean_box(0);
v_buckets_x27_173_ = lean_array_uset(v_buckets_133_, v___x_150_, v___x_172_);
lean_inc(v_a_124_);
v_bkt_x27_174_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_122_, v_a_124_, v_bkt_151_);
v___x_175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_124_, v_bkt_x27_174_);
lean_dec(v_a_124_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_sub(v_size_132_, v___x_176_);
lean_dec(v_size_132_);
v___y_126_ = v___x_150_;
v___y_127_ = v_buckets_x27_173_;
v___y_128_ = v_bkt_x27_174_;
v___y_129_ = v___x_177_;
goto v___jp_125_;
}
else
{
v___y_126_ = v___x_150_;
v___y_127_ = v_buckets_x27_173_;
v___y_128_ = v_bkt_x27_174_;
v___y_129_ = v_size_132_;
goto v___jp_125_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_181_, lean_object* v_as_182_, size_t v_sz_183_, size_t v_i_184_, lean_object* v_b_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_usize_dec_lt(v_i_184_, v_sz_183_);
if (v___x_186_ == 0)
{
lean_dec(v_val_181_);
return v_b_185_;
}
else
{
lean_object* v_a_187_; lean_object* v_declName_188_; lean_object* v___x_189_; size_t v___x_190_; size_t v___x_191_; 
v_a_187_ = lean_array_uget_borrowed(v_as_182_, v_i_184_);
v_declName_188_ = lean_ctor_get(v_a_187_, 1);
lean_inc(v_declName_188_);
lean_inc(v_val_181_);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_181_, v_b_185_, v_declName_188_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_184_, v___x_190_);
v_i_184_ = v___x_191_;
v_b_185_ = v___x_189_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_181_ = stack[0].m_obj;
lean_object* v_as_182_ = stack[1].m_obj;
size_t v_sz_183_ = stack[2].m_num;
size_t v_i_184_ = stack[3].m_num;
lean_object* v_b_185_ = stack[4].m_obj;
lean_object* v_res_193_;
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_181_, v_as_182_, v_sz_183_, v_i_184_, v_b_185_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_194_, lean_object* v_as_195_, lean_object* v_sz_196_, lean_object* v_i_197_, lean_object* v_b_198_){
_start:
{
size_t v_sz_boxed_199_; size_t v_i_boxed_200_; lean_object* v_res_201_; 
v_sz_boxed_199_ = lean_unbox_usize(v_sz_196_);
lean_dec(v_sz_196_);
v_i_boxed_200_ = lean_unbox_usize(v_i_197_);
lean_dec(v_i_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_194_, v_as_195_, v_sz_boxed_199_, v_i_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
return v_res_201_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_202_, size_t v_sz_203_, size_t v_i_204_, lean_object* v_b_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_206_ == 0)
{
return v_b_205_;
}
else
{
lean_object* v_snd_207_; 
v_snd_207_ = lean_ctor_get(v_b_205_, 1);
lean_inc(v_snd_207_);
if (lean_obj_tag(v_snd_207_) == 0)
{
lean_object* v_fst_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_fst_208_ = lean_ctor_get(v_b_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_b_205_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_b_205_, 1);
lean_dec(v_unused_216_);
v___x_210_ = v_b_205_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_fst_208_);
lean_dec(v_b_205_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_snd_207_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_fst_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_241_; 
v_fst_217_ = lean_ctor_get(v_b_205_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_b_205_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_b_205_, 1);
lean_dec(v_unused_242_);
v___x_219_ = v_b_205_;
v_isShared_220_ = v_isSharedCheck_241_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_fst_217_);
lean_dec(v_b_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_241_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_val_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_240_; 
v_val_221_ = lean_ctor_get(v_snd_207_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_snd_207_);
if (v_isSharedCheck_240_ == 0)
{
v___x_223_ = v_snd_207_;
v_isShared_224_ = v_isSharedCheck_240_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_val_221_);
lean_dec(v_snd_207_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_240_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v_a_225_ = lean_array_uget_borrowed(v_as_202_, v_i_204_);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_val_221_, v___x_226_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_227_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_239_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
size_t v_sz_230_; size_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v_sz_230_ = lean_array_size(v_a_225_);
v___x_231_ = ((size_t)0ULL);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_221_, v_a_225_, v_sz_230_, v___x_231_, v_fst_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_229_);
lean_ctor_set(v___x_219_, 0, v___x_232_);
v___x_234_ = v___x_219_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_229_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
size_t v___x_235_; size_t v___x_236_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_204_, v___x_235_);
v_i_204_ = v___x_236_;
v_b_205_ = v___x_234_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_202_ = stack[0].m_obj;
size_t v_sz_203_ = stack[1].m_num;
size_t v_i_204_ = stack[2].m_num;
lean_object* v_b_205_ = stack[3].m_obj;
lean_object* v_res_243_;
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_202_, v_sz_203_, v_i_204_, v_b_205_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_244_, lean_object* v_sz_245_, lean_object* v_i_246_, lean_object* v_b_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_245_);
lean_dec(v_sz_245_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_244_, v_sz_boxed_248_, v_i_boxed_249_, v_b_247_);
lean_dec_ref(v_as_244_);
return v_res_250_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
v___x_252_ = lean_unsigned_to_nat(16u);
v___x_253_ = lean_mk_array(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_s_256_; 
v___x_254_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_255_ = lean_unsigned_to_nat(0u);
v_s_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_256_, 0, v___x_255_);
lean_ctor_set(v_s_256_, 1, v___x_254_);
return v_s_256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_259_; lean_object* v_s_260_; lean_object* v___x_261_; 
v___x_259_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_260_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_s_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_262_){
_start:
{
lean_object* v___x_263_; size_t v_sz_264_; size_t v___x_265_; lean_object* v___x_266_; lean_object* v_fst_267_; 
v___x_263_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_264_ = lean_array_size(v_es_262_);
v___x_265_ = ((size_t)0ULL);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_262_, v_sz_264_, v___x_265_, v___x_263_);
v_fst_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_fst_267_);
lean_dec_ref(v___x_266_);
return v_fst_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_268_);
lean_dec_ref(v_es_268_);
return v_res_269_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_288_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_289_;
v_res_289_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_291_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_292_, lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_293_, v_x_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_293_ = stack[1].m_obj;
lean_object* v_x_294_ = stack[2].m_obj;
uint8_t v_res_296_;
v_res_296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_a_293_, v_x_294_);
stack->m_num = v_res_296_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_297_, lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_297_, v_a_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec(v_a_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_302_, lean_object* v_data_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_305_, lean_object* v_i_306_, lean_object* v_source_307_, lean_object* v_target_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_306_, v_source_307_, v_target_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_311_, v_x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_HashMap_instInhabited___redArg();
return v___x_314_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_318_, lean_object* v_modIdx_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__1, &l_Lean_getIndirectModUses___closed__1_once, _init_l_Lean_getIndirectModUses___closed__1);
v___x_321_ = l_Lean_indirectModUseExt;
v___x_322_ = 0;
v___x_323_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_320_, v___x_321_, v_env_318_, v_modIdx_319_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_324_, lean_object* v_modIdx_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_getIndirectModUses(v_env_324_, v_modIdx_325_);
lean_dec(v_modIdx_325_);
lean_dec_ref(v_env_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_addEntryFn_330_; lean_object* v_importedEntries_331_; lean_object* v_state_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_addEntryFn_330_ = lean_ctor_get(v___x_327_, 3);
lean_inc(v_addEntryFn_330_);
lean_dec_ref(v___x_327_);
v_importedEntries_331_ = lean_ctor_get(v_s_329_, 0);
v_state_332_ = lean_ctor_get(v_s_329_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_s_329_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v_s_329_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_state_332_);
lean_inc(v_importedEntries_331_);
lean_dec(v_s_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_state_336_; lean_object* v___x_338_; 
v_state_336_ = lean_apply_2(v_addEntryFn_330_, v_state_332_, v___x_328_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v_state_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_importedEntries_331_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_state_336_);
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
lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v___x_341_, lean_object* v___f_342_, uint8_t v___x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_toEnvExtension_345_; lean_object* v_asyncMode_346_; uint8_t v_logWrites_347_; lean_object* v___x_348_; 
v_toEnvExtension_345_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_toEnvExtension_345_);
lean_dec_ref(v___x_341_);
v_asyncMode_346_ = lean_ctor_get(v_toEnvExtension_345_, 2);
lean_inc(v_asyncMode_346_);
v_logWrites_347_ = lean_ctor_get_uint8(v_toEnvExtension_345_, sizeof(void*)*6);
v___x_348_ = lean_box(0);
if (v_logWrites_347_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_345_, v_x_344_, v___f_342_, v_asyncMode_346_, v___x_348_, v___x_343_);
lean_dec(v_asyncMode_346_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_inc_ref(v_toEnvExtension_345_);
v___x_350_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_345_, v_x_344_);
lean_dec_ref(v_x_344_);
v___x_351_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_345_, v___x_350_, v___f_342_, v_asyncMode_346_, v___x_348_, v___x_343_);
lean_dec(v_asyncMode_346_);
return v___x_351_;
}
}
}
LEAN_EXPORT void l_Lean_recordIndirectModUse___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_341_ = stack[0].m_obj;
lean_object* v___f_342_ = stack[1].m_obj;
uint8_t v___x_343_ = stack[2].m_num;
lean_object* v_x_344_ = stack[3].m_obj;
lean_object* v_res_352_;
v_res_352_ = l_Lean_recordIndirectModUse___redArg___lam__1(v___x_341_, v___f_342_, v___x_343_, v_x_344_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1___boxed(lean_object* v___x_353_, lean_object* v___f_354_, lean_object* v___x_355_, lean_object* v_x_356_){
_start:
{
uint8_t v___x_434__boxed_357_; lean_object* v_res_358_; 
v___x_434__boxed_357_ = lean_unbox(v___x_355_);
v_res_358_ = l_Lean_recordIndirectModUse___redArg___lam__1(v___x_353_, v___f_354_, v___x_434__boxed_357_, v_x_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_modifyEnv_359_, lean_object* v___f_360_, lean_object* v_____r_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_apply_1(v_modifyEnv_359_, v___f_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_toPure_366_, lean_object* v_cls_367_, lean_object* v_____do__lift_368_, lean_object* v_____do__lift_369_){
_start:
{
uint8_t v_hasTrace_370_; 
v_hasTrace_370_ = lean_ctor_get_uint8(v_____do__lift_369_, sizeof(void*)*1);
if (v_hasTrace_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_cls_367_);
v___x_371_ = lean_box(v_hasTrace_370_);
v___x_372_ = lean_apply_2(v_toPure_366_, lean_box(0), v___x_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_373_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_374_ = l_Lean_Name_append(v___x_373_, v_cls_367_);
v___x_375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_368_, v_____do__lift_369_, v___x_374_);
lean_dec(v___x_374_);
v___x_376_ = lean_box(v___x_375_);
v___x_377_ = lean_apply_2(v_toPure_366_, lean_box(0), v___x_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object* v_toPure_378_, lean_object* v_cls_379_, lean_object* v_____do__lift_380_, lean_object* v_____do__lift_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_recordIndirectModUse___redArg___lam__3(v_toPure_378_, v_cls_379_, v_____do__lift_380_, v_____do__lift_381_);
lean_dec_ref(v_____do__lift_381_);
lean_dec_ref(v_____do__lift_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_inst_383_, lean_object* v_toPure_384_, lean_object* v_cls_385_, lean_object* v_toBind_386_, lean_object* v_____do__lift_387_){
_start:
{
lean_object* v_getOptionsUnrestricted_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v_getOptionsUnrestricted_388_ = lean_ctor_get(v_inst_383_, 1);
lean_inc(v_getOptionsUnrestricted_388_);
lean_dec_ref(v_inst_383_);
v___f_389_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_389_, 0, v_toPure_384_);
lean_closure_set(v___f_389_, 1, v_cls_385_);
lean_closure_set(v___f_389_, 2, v_____do__lift_387_);
v___x_390_ = lean_apply_4(v_toBind_386_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_388_, v___f_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__2));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__4));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v_modifyEnv_400_, lean_object* v___f_401_, lean_object* v_declName_402_, lean_object* v_kind_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_cls_408_, lean_object* v_toBind_409_, lean_object* v___f_410_, uint8_t v_____do__lift_411_){
_start:
{
if (v_____do__lift_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v___f_410_);
lean_dec(v_toBind_409_);
lean_dec(v_cls_408_);
lean_dec(v_inst_407_);
lean_dec_ref(v_inst_406_);
lean_dec_ref(v_inst_405_);
lean_dec_ref(v_inst_404_);
lean_dec_ref(v_kind_403_);
lean_dec(v_declName_402_);
v___x_412_ = lean_apply_1(v_modifyEnv_400_, v___f_401_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v___f_401_);
lean_dec(v_modifyEnv_400_);
v___x_413_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__5___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__1);
v___x_414_ = l_Lean_MessageData_ofName(v_declName_402_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__5___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__5___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__3);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_stringToMessageData(v_kind_403_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__5___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__5___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__5___closed__5);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = l_Lean_addTrace___redArg(v_inst_404_, v_inst_405_, v_inst_406_, v_inst_407_, v_cls_408_, v___x_421_);
v___x_423_ = lean_apply_4(v_toBind_409_, lean_box(0), lean_box(0), v___x_422_, v___f_410_);
return v___x_423_;
}
}
}
LEAN_EXPORT void l_Lean_recordIndirectModUse___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifyEnv_400_ = stack[0].m_obj;
lean_object* v___f_401_ = stack[1].m_obj;
lean_object* v_declName_402_ = stack[2].m_obj;
lean_object* v_kind_403_ = stack[3].m_obj;
lean_object* v_inst_404_ = stack[4].m_obj;
lean_object* v_inst_405_ = stack[5].m_obj;
lean_object* v_inst_406_ = stack[6].m_obj;
lean_object* v_inst_407_ = stack[7].m_obj;
lean_object* v_cls_408_ = stack[8].m_obj;
lean_object* v_toBind_409_ = stack[9].m_obj;
lean_object* v___f_410_ = stack[10].m_obj;
uint8_t v_____do__lift_411_ = stack[11].m_num;
lean_object* v_res_424_;
v_res_424_ = l_Lean_recordIndirectModUse___redArg___lam__5(v_modifyEnv_400_, v___f_401_, v_declName_402_, v_kind_403_, v_inst_404_, v_inst_405_, v_inst_406_, v_inst_407_, v_cls_408_, v_toBind_409_, v___f_410_, v_____do__lift_411_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___boxed(lean_object* v_modifyEnv_425_, lean_object* v___f_426_, lean_object* v_declName_427_, lean_object* v_kind_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_cls_433_, lean_object* v_toBind_434_, lean_object* v___f_435_, lean_object* v_____do__lift_436_){
_start:
{
uint8_t v_____do__lift_561__boxed_437_; lean_object* v_res_438_; 
v_____do__lift_561__boxed_437_ = lean_unbox(v_____do__lift_436_);
v_res_438_ = l_Lean_recordIndirectModUse___redArg___lam__5(v_modifyEnv_425_, v___f_426_, v_declName_427_, v_kind_428_, v_inst_429_, v_inst_430_, v_inst_431_, v_inst_432_, v_cls_433_, v_toBind_434_, v___f_435_, v_____do__lift_561__boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__6(lean_object* v___x_442_, lean_object* v_kind_443_, lean_object* v_declName_444_, lean_object* v___x_445_, lean_object* v_inst_446_, lean_object* v_modifyEnv_447_, lean_object* v_inst_448_, lean_object* v_toPure_449_, lean_object* v_toBind_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_____do__lift_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_455_ = l_Lean_indirectModUseExt;
v___x_456_ = lean_box(2);
v___x_457_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_442_, v___x_455_, v_____do__lift_454_, v___x_456_);
lean_inc(v_declName_444_);
lean_inc_ref(v_kind_443_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_kind_443_);
lean_ctor_set(v___x_458_, 1, v_declName_444_);
lean_inc_ref(v___x_458_);
v___x_459_ = l_List_elem___redArg(v___x_445_, v___x_458_, v___x_457_);
if (v___x_459_ == 0)
{
lean_object* v_getInheritedTraceOptions_460_; lean_object* v___f_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v_cls_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_getInheritedTraceOptions_460_ = lean_ctor_get(v_inst_446_, 2);
lean_inc(v_getInheritedTraceOptions_460_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_461_, 0, v___x_455_);
lean_closure_set(v___f_461_, 1, v___x_458_);
v___x_462_ = 1;
v___x_463_ = lean_box(v___x_462_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_464_, 0, v___x_455_);
lean_closure_set(v___f_464_, 1, v___f_461_);
lean_closure_set(v___f_464_, 2, v___x_463_);
lean_inc_ref(v___f_464_);
lean_inc(v_modifyEnv_447_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2), 3, 2);
lean_closure_set(v___f_465_, 0, v_modifyEnv_447_);
lean_closure_set(v___f_465_, 1, v___f_464_);
v_cls_466_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__6___closed__1));
lean_inc_n(v_toBind_450_, 3);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_467_, 0, v_inst_448_);
lean_closure_set(v___f_467_, 1, v_toPure_449_);
lean_closure_set(v___f_467_, 2, v_cls_466_);
lean_closure_set(v___f_467_, 3, v_toBind_450_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_468_, 0, v_modifyEnv_447_);
lean_closure_set(v___f_468_, 1, v___f_464_);
lean_closure_set(v___f_468_, 2, v_declName_444_);
lean_closure_set(v___f_468_, 3, v_kind_443_);
lean_closure_set(v___f_468_, 4, v_inst_451_);
lean_closure_set(v___f_468_, 5, v_inst_446_);
lean_closure_set(v___f_468_, 6, v_inst_452_);
lean_closure_set(v___f_468_, 7, v_inst_453_);
lean_closure_set(v___f_468_, 8, v_cls_466_);
lean_closure_set(v___f_468_, 9, v_toBind_450_);
lean_closure_set(v___f_468_, 10, v___f_465_);
v___x_469_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_460_, v___f_467_);
v___x_470_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_469_, v___f_468_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref_known(v___x_458_, 2);
lean_dec(v_inst_453_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_inst_451_);
lean_dec(v_toBind_450_);
lean_dec_ref(v_inst_448_);
lean_dec(v_modifyEnv_447_);
lean_dec_ref(v_inst_446_);
lean_dec(v_declName_444_);
lean_dec_ref(v_kind_443_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_apply_2(v_toPure_449_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_kind_479_, lean_object* v_declName_480_){
_start:
{
lean_object* v_toApplicative_481_; lean_object* v_toBind_482_; lean_object* v_getEnv_483_; lean_object* v_modifyEnv_484_; lean_object* v_toPure_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___f_488_; lean_object* v___x_489_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_473_, 0);
v_toBind_482_ = lean_ctor_get(v_inst_473_, 1);
lean_inc_n(v_toBind_482_, 2);
v_getEnv_483_ = lean_ctor_get(v_inst_474_, 0);
lean_inc(v_getEnv_483_);
v_modifyEnv_484_ = lean_ctor_get(v_inst_474_, 1);
lean_inc(v_modifyEnv_484_);
lean_dec_ref(v_inst_474_);
v_toPure_485_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_485_);
v___x_486_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_487_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___f_488_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__6), 13, 12);
lean_closure_set(v___f_488_, 0, v___x_487_);
lean_closure_set(v___f_488_, 1, v_kind_479_);
lean_closure_set(v___f_488_, 2, v_declName_480_);
lean_closure_set(v___f_488_, 3, v___x_486_);
lean_closure_set(v___f_488_, 4, v_inst_475_);
lean_closure_set(v___f_488_, 5, v_modifyEnv_484_);
lean_closure_set(v___f_488_, 6, v_inst_476_);
lean_closure_set(v___f_488_, 7, v_toPure_485_);
lean_closure_set(v___f_488_, 8, v_toBind_482_);
lean_closure_set(v___f_488_, 9, v_inst_473_);
lean_closure_set(v___f_488_, 10, v_inst_477_);
lean_closure_set(v___f_488_, 11, v_inst_478_);
v___x_489_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v_getEnv_483_, v___f_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_kind_497_, lean_object* v_declName_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_recordIndirectModUse___redArg(v_inst_491_, v_inst_492_, v_inst_493_, v_inst_494_, v_inst_495_, v_inst_496_, v_kind_497_, v_declName_498_);
return v___x_499_;
}
}
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_module_502_; uint8_t v_isExported_503_; uint8_t v_isMeta_504_; lean_object* v_module_505_; uint8_t v_isExported_506_; uint8_t v_isMeta_507_; uint8_t v___y_509_; uint8_t v___x_510_; 
v_module_502_ = lean_ctor_get(v_x_500_, 0);
v_isExported_503_ = lean_ctor_get_uint8(v_x_500_, sizeof(void*)*1);
v_isMeta_504_ = lean_ctor_get_uint8(v_x_500_, sizeof(void*)*1 + 1);
v_module_505_ = lean_ctor_get(v_x_501_, 0);
v_isExported_506_ = lean_ctor_get_uint8(v_x_501_, sizeof(void*)*1);
v_isMeta_507_ = lean_ctor_get_uint8(v_x_501_, sizeof(void*)*1 + 1);
v___x_510_ = lean_name_eq(v_module_502_, v_module_505_);
if (v___x_510_ == 0)
{
return v___x_510_;
}
else
{
if (v_isExported_506_ == 0)
{
if (v_isExported_503_ == 0)
{
v___y_509_ = v___x_510_;
goto v___jp_508_;
}
else
{
return v_isExported_506_;
}
}
else
{
v___y_509_ = v_isExported_503_;
goto v___jp_508_;
}
}
v___jp_508_:
{
if (v___y_509_ == 0)
{
return v___y_509_;
}
else
{
if (v_isMeta_507_ == 0)
{
if (v_isMeta_504_ == 0)
{
return v___y_509_;
}
else
{
return v_isMeta_507_;
}
}
else
{
return v_isMeta_504_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqExtraModUse_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_500_ = stack[0].m_obj;
lean_object* v_x_501_ = stack[1].m_obj;
uint8_t v_res_511_;
v_res_511_ = l_Lean_instBEqExtraModUse_beq(v_x_500_, v_x_501_);
stack->m_num = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Lean_instBEqExtraModUse_beq(v_x_512_, v_x_513_);
lean_dec_ref(v_x_513_);
lean_dec_ref(v_x_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_518_){
_start:
{
lean_object* v_module_519_; uint8_t v_isExported_520_; uint8_t v_isMeta_521_; uint64_t v___y_523_; uint64_t v___y_524_; uint64_t v___x_530_; uint64_t v___y_532_; 
v_module_519_ = lean_ctor_get(v_x_518_, 0);
v_isExported_520_ = lean_ctor_get_uint8(v_x_518_, sizeof(void*)*1);
v_isMeta_521_ = lean_ctor_get_uint8(v_x_518_, sizeof(void*)*1 + 1);
v___x_530_ = 0ULL;
if (lean_obj_tag(v_module_519_) == 0)
{
uint64_t v___x_536_; 
v___x_536_ = 1723ULL;
v___y_532_ = v___x_536_;
goto v___jp_531_;
}
else
{
uint64_t v_hash_537_; 
v_hash_537_ = lean_ctor_get_uint64(v_module_519_, sizeof(void*)*2);
v___y_532_ = v_hash_537_;
goto v___jp_531_;
}
v___jp_522_:
{
uint64_t v___x_525_; 
v___x_525_ = lean_uint64_mix_hash(v___y_523_, v___y_524_);
if (v_isMeta_521_ == 0)
{
uint64_t v___x_526_; uint64_t v___x_527_; 
v___x_526_ = 13ULL;
v___x_527_ = lean_uint64_mix_hash(v___x_525_, v___x_526_);
return v___x_527_;
}
else
{
uint64_t v___x_528_; uint64_t v___x_529_; 
v___x_528_ = 11ULL;
v___x_529_ = lean_uint64_mix_hash(v___x_525_, v___x_528_);
return v___x_529_;
}
}
v___jp_531_:
{
uint64_t v___x_533_; 
v___x_533_ = lean_uint64_mix_hash(v___x_530_, v___y_532_);
if (v_isExported_520_ == 0)
{
uint64_t v___x_534_; 
v___x_534_ = 13ULL;
v___y_523_ = v___x_533_;
v___y_524_ = v___x_534_;
goto v___jp_522_;
}
else
{
uint64_t v___x_535_; 
v___x_535_ = 11ULL;
v___y_523_ = v___x_533_;
v___y_524_ = v___x_535_;
goto v___jp_522_;
}
}
}
}
LEAN_EXPORT void l_Lean_instHashableExtraModUse_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_518_ = stack[0].m_obj;
uint64_t v_res_538_;
v_res_538_ = l_Lean_instHashableExtraModUse_hash(v_x_518_);
stack->m_num = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_539_){
_start:
{
uint64_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Lean_instHashableExtraModUse_hash(v_x_539_);
lean_dec_ref(v_x_539_);
v_r_541_ = lean_box_uint64(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_nat_to_int(v_a_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(10u);
v___x_560_ = lean_nat_to_int(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(14u);
v___x_568_ = lean_nat_to_int(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_574_ = lean_string_length(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_576_ = lean_nat_to_int(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_581_){
_start:
{
lean_object* v_module_582_; uint8_t v_isExported_583_; uint8_t v_isMeta_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_module_582_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_module_582_);
v_isExported_583_ = lean_ctor_get_uint8(v_x_581_, sizeof(void*)*1);
v_isMeta_584_ = lean_ctor_get_uint8(v_x_581_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_581_);
v___x_585_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_586_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_587_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = l_Lean_Name_reprPrec(v_module_582_, v___x_588_);
v___x_590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = 0;
v___x_592_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*1, v___x_591_);
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_586_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_box(1);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_585_);
v___x_601_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_602_ = l_Bool_repr___redArg(v_isExported_583_);
v___x_603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*1, v___x_591_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_600_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_594_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_596_);
v___x_608_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_585_);
v___x_611_ = l_Bool_repr___redArg(v_isMeta_584_);
v___x_612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_587_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*1, v___x_591_);
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_610_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_616_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_614_);
v___x_618_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_615_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*1, v___x_591_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_622_, lean_object* v_prec_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_625_, lean_object* v_prec_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_instReprExtraModUse_repr(v_x_625_, v_prec_626_);
lean_dec(v_prec_626_);
return v_res_627_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_630_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg(){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1);
return v___x_634_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_635_;
v_res_635_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___dummy_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
return v_res_637_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_entries_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_647_ = lean_array_mk(v_entries_645_);
v___x_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_entries_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_649_, v_x_650_, v_entries_651_);
lean_dec_ref(v_x_650_);
lean_dec_ref(v_x_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_array_mk(v_es_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_657_);
lean_dec_ref(v_x_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_ks_663_; lean_object* v_vs_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_688_; 
v_ks_663_ = lean_ctor_get(v_x_659_, 0);
v_vs_664_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_688_ == 0)
{
v___x_666_ = v_x_659_;
v_isShared_667_ = v_isSharedCheck_688_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_vs_664_);
lean_inc(v_ks_663_);
lean_dec(v_x_659_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_688_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_ks_663_);
v___x_669_ = lean_nat_dec_lt(v_x_660_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v_x_660_);
v___x_670_ = lean_array_push(v_ks_663_, v_x_661_);
v___x_671_ = lean_array_push(v_vs_664_, v_x_662_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_671_);
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
lean_object* v_k_x27_675_; uint8_t v___x_676_; 
v_k_x27_675_ = lean_array_fget_borrowed(v_ks_663_, v_x_660_);
v___x_676_ = l_Lean_instBEqExtraModUse_beq(v_x_661_, v_k_x27_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; 
if (v_isShared_667_ == 0)
{
v___x_678_ = v___x_666_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_ks_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_vs_664_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_x_660_, v___x_679_);
lean_dec(v_x_660_);
v_x_659_ = v___x_678_;
v_x_660_ = v___x_680_;
goto _start;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = lean_array_fset(v_ks_663_, v_x_660_, v_x_661_);
v___x_684_ = lean_array_fset(v_vs_664_, v_x_660_, v_x_662_);
lean_dec(v_x_660_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_684_);
lean_ctor_set(v___x_666_, 0, v___x_683_);
v___x_686_ = v___x_666_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_689_, lean_object* v_k_690_, lean_object* v_v_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_689_, v___x_692_, v_k_690_, v_v_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_694_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_695_, size_t v_x_696_, size_t v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_695_) == 0)
{
lean_object* v_es_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v_j_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_es_700_ = lean_ctor_get(v_x_695_, 0);
v___x_701_ = ((size_t)31ULL);
v___x_702_ = lean_usize_land(v_x_696_, v___x_701_);
v_j_703_ = lean_usize_to_nat(v___x_702_);
v___x_704_ = lean_array_get_size(v_es_700_);
v___x_705_ = lean_nat_dec_lt(v_j_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec(v_j_703_);
lean_dec(v_x_699_);
lean_dec_ref(v_x_698_);
return v_x_695_;
}
else
{
lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_744_; 
lean_inc_ref(v_es_700_);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_695_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_x_695_, 0);
lean_dec(v_unused_745_);
v___x_707_ = v_x_695_;
v_isShared_708_ = v_isSharedCheck_744_;
goto v_resetjp_706_;
}
else
{
lean_dec(v_x_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_744_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_v_709_; lean_object* v___x_710_; lean_object* v_xs_x27_711_; lean_object* v___y_713_; 
v_v_709_ = lean_array_fget(v_es_700_, v_j_703_);
v___x_710_ = lean_box(0);
v_xs_x27_711_ = lean_array_fset(v_es_700_, v_j_703_, v___x_710_);
switch(lean_obj_tag(v_v_709_))
{
case 0:
{
lean_object* v_key_718_; lean_object* v_val_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_729_; 
v_key_718_ = lean_ctor_get(v_v_709_, 0);
v_val_719_ = lean_ctor_get(v_v_709_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_v_709_);
if (v_isSharedCheck_729_ == 0)
{
v___x_721_ = v_v_709_;
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_val_719_);
lean_inc(v_key_718_);
lean_dec(v_v_709_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_instBEqExtraModUse_beq(v_x_698_, v_key_718_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_del_object(v___x_721_);
v___x_724_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_718_, v_val_719_, v_x_698_, v_x_699_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___y_713_ = v___x_725_;
goto v___jp_712_;
}
else
{
lean_object* v___x_727_; 
lean_dec(v_val_719_);
lean_dec(v_key_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_x_699_);
lean_ctor_set(v___x_721_, 0, v_x_698_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_x_698_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_x_699_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v___y_713_ = v___x_727_;
goto v___jp_712_;
}
}
}
}
case 1:
{
lean_object* v_node_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_742_; 
v_node_730_ = lean_ctor_get(v_v_709_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v_v_709_);
if (v_isSharedCheck_742_ == 0)
{
v___x_732_ = v_v_709_;
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_node_730_);
lean_dec(v_v_709_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_734_ = ((size_t)5ULL);
v___x_735_ = lean_usize_shift_right(v_x_696_, v___x_734_);
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_add(v_x_697_, v___x_736_);
v___x_738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_730_, v___x_735_, v___x_737_, v_x_698_, v_x_699_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_738_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v___y_713_ = v___x_740_;
goto v___jp_712_;
}
}
}
default: 
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_x_698_);
lean_ctor_set(v___x_743_, 1, v_x_699_);
v___y_713_ = v___x_743_;
goto v___jp_712_;
}
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_array_fset(v_xs_x27_711_, v_j_703_, v___y_713_);
lean_dec(v_j_703_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_714_);
v___x_716_ = v___x_707_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v_ks_746_; lean_object* v_vs_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_765_; 
v_ks_746_ = lean_ctor_get(v_x_695_, 0);
v_vs_747_ = lean_ctor_get(v_x_695_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_695_);
if (v_isSharedCheck_765_ == 0)
{
v___x_749_ = v_x_695_;
v_isShared_750_ = v_isSharedCheck_765_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_vs_747_);
lean_inc(v_ks_746_);
lean_dec(v_x_695_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_765_;
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
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_746_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_747_);
v___x_752_ = v_reuseFailAlloc_764_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v_newNode_753_; size_t v___x_754_; uint8_t v___x_755_; 
v_newNode_753_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_752_, v_x_698_, v_x_699_);
v___x_754_ = ((size_t)7ULL);
v___x_755_ = lean_usize_dec_le(v___x_754_, v_x_697_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_753_);
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
lean_dec(v___x_756_);
if (v___x_758_ == 0)
{
lean_object* v_ks_759_; lean_object* v_vs_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_ks_759_ = lean_ctor_get(v_newNode_753_, 0);
lean_inc_ref(v_ks_759_);
v_vs_760_ = lean_ctor_get(v_newNode_753_, 1);
lean_inc_ref(v_vs_760_);
lean_dec_ref(v_newNode_753_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_697_, v_ks_759_, v_vs_760_, v___x_761_, v___x_762_);
lean_dec_ref(v_vs_760_);
lean_dec_ref(v_ks_759_);
return v___x_763_;
}
else
{
return v_newNode_753_;
}
}
else
{
return v_newNode_753_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_695_ = stack[0].m_obj;
size_t v_x_696_ = stack[1].m_num;
size_t v_x_697_ = stack[2].m_num;
lean_object* v_x_698_ = stack[3].m_obj;
lean_object* v_x_699_ = stack[4].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_695_, v_x_696_, v_x_697_, v_x_698_, v_x_699_);
stack->m_obj
 = v_res_766_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_767_, lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_i_770_, lean_object* v_entries_771_){
_start:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_array_get_size(v_keys_768_);
v___x_773_ = lean_nat_dec_lt(v_i_770_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_i_770_);
return v_entries_771_;
}
else
{
lean_object* v_k_774_; lean_object* v_v_775_; uint64_t v___x_776_; size_t v_h_777_; size_t v___x_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v_h_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_k_774_ = lean_array_fget_borrowed(v_keys_768_, v_i_770_);
v_v_775_ = lean_array_fget_borrowed(v_vals_769_, v_i_770_);
v___x_776_ = l_Lean_instHashableExtraModUse_hash(v_k_774_);
v_h_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = ((size_t)5ULL);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_sub(v_depth_767_, v___x_780_);
v___x_782_ = lean_usize_mul(v___x_778_, v___x_781_);
v_h_783_ = lean_usize_shift_right(v_h_777_, v___x_782_);
v___x_784_ = lean_nat_add(v_i_770_, v___x_779_);
lean_dec(v_i_770_);
lean_inc(v_v_775_);
lean_inc(v_k_774_);
v___x_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_771_, v_h_783_, v_depth_767_, v_k_774_, v_v_775_);
v_i_770_ = v___x_784_;
v_entries_771_ = v___x_785_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_767_ = stack[0].m_num;
lean_object* v_keys_768_ = stack[1].m_obj;
lean_object* v_vals_769_ = stack[2].m_obj;
lean_object* v_i_770_ = stack[3].m_obj;
lean_object* v_entries_771_ = stack[4].m_obj;
lean_object* v_res_787_;
v_res_787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_767_, v_keys_768_, v_vals_769_, v_i_770_, v_entries_771_);
stack->m_obj
 = v_res_787_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_i_791_, lean_object* v_entries_792_){
_start:
{
size_t v_depth_boxed_793_; lean_object* v_res_794_; 
v_depth_boxed_793_ = lean_unbox_usize(v_depth_788_);
lean_dec(v_depth_788_);
v_res_794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_793_, v_keys_789_, v_vals_790_, v_i_791_, v_entries_792_);
lean_dec_ref(v_vals_790_);
lean_dec_ref(v_keys_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
size_t v_x_632__boxed_800_; size_t v_x_633__boxed_801_; lean_object* v_res_802_; 
v_x_632__boxed_800_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_x_633__boxed_801_ = lean_unbox_usize(v_x_797_);
lean_dec(v_x_797_);
v_res_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_795_, v_x_632__boxed_800_, v_x_633__boxed_801_, v_x_798_, v_x_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_806_ = l_Lean_instHashableExtraModUse_hash(v_x_804_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_803_, v___x_807_, v___x_808_, v_x_804_, v_x_805_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_810_, lean_object* v_k_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_box(0);
v___x_813_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_810_, v_k_811_, v___x_812_);
return v___x_813_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_814_, lean_object* v_i_815_, lean_object* v_k_816_){
_start:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_get_size(v_keys_814_);
v___x_818_ = lean_nat_dec_lt(v_i_815_, v___x_817_);
if (v___x_818_ == 0)
{
lean_dec(v_i_815_);
return v___x_818_;
}
else
{
lean_object* v_k_x27_819_; uint8_t v___x_820_; 
v_k_x27_819_ = lean_array_fget_borrowed(v_keys_814_, v_i_815_);
v___x_820_ = l_Lean_instBEqExtraModUse_beq(v_k_816_, v_k_x27_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_i_815_, v___x_821_);
lean_dec(v_i_815_);
v_i_815_ = v___x_822_;
goto _start;
}
else
{
lean_dec(v_i_815_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_814_ = stack[0].m_obj;
lean_object* v_i_815_ = stack[1].m_obj;
lean_object* v_k_816_ = stack[2].m_obj;
uint8_t v_res_824_;
v_res_824_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_814_, v_i_815_, v_k_816_);
stack->m_num = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_825_, lean_object* v_i_826_, lean_object* v_k_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_825_, v_i_826_, v_k_827_);
lean_dec_ref(v_k_827_);
lean_dec_ref(v_keys_825_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_830_, size_t v_x_831_, lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_es_833_; lean_object* v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_j_837_; lean_object* v___x_838_; 
v_es_833_ = lean_ctor_get(v_x_830_, 0);
v___x_834_ = lean_box(2);
v___x_835_ = ((size_t)31ULL);
v___x_836_ = lean_usize_land(v_x_831_, v___x_835_);
v_j_837_ = lean_usize_to_nat(v___x_836_);
v___x_838_ = lean_array_get_borrowed(v___x_834_, v_es_833_, v_j_837_);
lean_dec(v_j_837_);
switch(lean_obj_tag(v___x_838_))
{
case 0:
{
lean_object* v_key_839_; uint8_t v___x_840_; 
v_key_839_ = lean_ctor_get(v___x_838_, 0);
v___x_840_ = l_Lean_instBEqExtraModUse_beq(v_x_832_, v_key_839_);
return v___x_840_;
}
case 1:
{
lean_object* v_node_841_; size_t v___x_842_; size_t v___x_843_; 
v_node_841_ = lean_ctor_get(v___x_838_, 0);
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_usize_shift_right(v_x_831_, v___x_842_);
v_x_830_ = v_node_841_;
v_x_831_ = v___x_843_;
goto _start;
}
default: 
{
uint8_t v___x_845_; 
v___x_845_ = 0;
return v___x_845_;
}
}
}
else
{
lean_object* v_ks_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_ks_846_ = lean_ctor_get(v_x_830_, 0);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_846_, v___x_847_, v_x_832_);
return v___x_848_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_830_ = stack[0].m_obj;
size_t v_x_831_ = stack[1].m_num;
lean_object* v_x_832_ = stack[2].m_obj;
uint8_t v_res_849_;
v_res_849_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_830_, v_x_831_, v_x_832_);
stack->m_num = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
size_t v_x_913__boxed_853_; uint8_t v_res_854_; lean_object* v_r_855_; 
v_x_913__boxed_853_ = lean_unbox_usize(v_x_851_);
lean_dec(v_x_851_);
v_res_854_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_850_, v_x_913__boxed_853_, v_x_852_);
lean_dec_ref(v_x_852_);
lean_dec_ref(v_x_850_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
uint64_t v___x_858_; size_t v___x_859_; uint8_t v___x_860_; 
v___x_858_ = l_Lean_instHashableExtraModUse_hash(v_x_857_);
v___x_859_ = lean_uint64_to_usize(v___x_858_);
v___x_860_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_856_, v___x_859_, v_x_857_);
return v___x_860_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_856_ = stack[0].m_obj;
lean_object* v_x_857_ = stack[1].m_obj;
uint8_t v_res_861_;
v_res_861_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_856_, v_x_857_);
stack->m_num = v_res_861_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_862_, v_x_863_);
lean_dec_ref(v_x_863_);
lean_dec_ref(v_x_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_909_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_910_;
v_res_910_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_912_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_914_, v_x_915_);
return v___x_916_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_914_ = stack[1].m_obj;
lean_object* v_x_915_ = stack[2].m_obj;
uint8_t v_res_917_;
v_res_917_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_box(0), v_x_914_, v_x_915_);
stack->m_num = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_918_, v_x_919_, v_x_920_);
lean_dec_ref(v_x_920_);
lean_dec_ref(v_x_919_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_924_, v_x_925_, v_x_926_);
return v___x_927_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_928_, lean_object* v_x_929_, size_t v_x_930_, lean_object* v_x_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_929_, v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_929_ = stack[1].m_obj;
size_t v_x_930_ = stack[2].m_num;
lean_object* v_x_931_ = stack[3].m_obj;
uint8_t v_res_933_;
v_res_933_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_x_929_, v_x_930_, v_x_931_);
stack->m_num = v_res_933_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
size_t v_x_1196__boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_x_1196__boxed_938_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_934_, v_x_935_, v_x_1196__boxed_938_, v_x_937_);
lean_dec_ref(v_x_937_);
lean_dec_ref(v_x_935_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, size_t v_x_943_, size_t v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_942_, v_x_943_, v_x_944_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_942_ = stack[1].m_obj;
size_t v_x_943_ = stack[2].m_num;
size_t v_x_944_ = stack[3].m_num;
lean_object* v_x_945_ = stack[4].m_obj;
lean_object* v_x_946_ = stack[5].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_box(0), v_x_942_, v_x_943_, v_x_944_, v_x_945_, v_x_946_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_1214__boxed_955_; size_t v_x_1215__boxed_956_; lean_object* v_res_957_; 
v_x_1214__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_x_1215__boxed_956_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_949_, v_x_950_, v_x_1214__boxed_955_, v_x_1215__boxed_956_, v_x_953_, v_x_954_);
return v_res_957_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_heq_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_959_, v_i_962_, v_k_963_);
return v___x_964_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_959_ = stack[1].m_obj;
lean_object* v_vals_960_ = stack[2].m_obj;
lean_object* v_i_962_ = stack[4].m_obj;
lean_object* v_k_963_ = stack[5].m_obj;
uint8_t v_res_965_;
v_res_965_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_box(0), v_keys_959_, v_vals_960_, lean_box(0), v_i_962_, v_k_963_);
stack->m_num = v_res_965_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_966_, lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_heq_969_, lean_object* v_i_970_, lean_object* v_k_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_966_, v_keys_967_, v_vals_968_, v_heq_969_, v_i_970_, v_k_971_);
lean_dec_ref(v_k_971_);
lean_dec_ref(v_vals_968_);
lean_dec_ref(v_keys_967_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_974_, lean_object* v_n_975_, lean_object* v_k_976_, lean_object* v_v_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_975_, v_k_976_, v_v_977_);
return v___x_978_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_979_, size_t v_depth_980_, lean_object* v_keys_981_, lean_object* v_vals_982_, lean_object* v_heq_983_, lean_object* v_i_984_, lean_object* v_entries_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_980_, v_keys_981_, v_vals_982_, v_i_984_, v_entries_985_);
return v___x_986_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_980_ = stack[1].m_num;
lean_object* v_keys_981_ = stack[2].m_obj;
lean_object* v_vals_982_ = stack[3].m_obj;
lean_object* v_i_984_ = stack[5].m_obj;
lean_object* v_entries_985_ = stack[6].m_obj;
lean_object* v_res_987_;
v_res_987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_box(0), v_depth_980_, v_keys_981_, v_vals_982_, lean_box(0), v_i_984_, v_entries_985_);
stack->m_obj
 = v_res_987_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_988_, lean_object* v_depth_989_, lean_object* v_keys_990_, lean_object* v_vals_991_, lean_object* v_heq_992_, lean_object* v_i_993_, lean_object* v_entries_994_){
_start:
{
size_t v_depth_boxed_995_; lean_object* v_res_996_; 
v_depth_boxed_995_ = lean_unbox_usize(v_depth_989_);
lean_dec(v_depth_989_);
v_res_996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_988_, v_depth_boxed_995_, v_keys_990_, v_vals_991_, v_heq_992_, v_i_993_, v_entries_994_);
lean_dec_ref(v_vals_991_);
lean_dec_ref(v_keys_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_1007_, lean_object* v_modIdx_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1009_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_1010_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1011_ = 0;
v___x_1012_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1009_, v___x_1010_, v_env_1007_, v_modIdx_1008_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_1013_, lean_object* v_modIdx_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_getExtraModUses(v_env_1013_, v_modIdx_1014_);
lean_dec(v_modIdx_1014_);
lean_dec_ref(v_env_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___lam__0(lean_object* v___x_1016_, lean_object* v_head_1017_, lean_object* v_s_1018_){
_start:
{
lean_object* v_addEntryFn_1019_; lean_object* v_importedEntries_1020_; lean_object* v_state_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_addEntryFn_1019_ = lean_ctor_get(v___x_1016_, 3);
lean_inc(v_addEntryFn_1019_);
lean_dec_ref(v___x_1016_);
v_importedEntries_1020_ = lean_ctor_get(v_s_1018_, 0);
v_state_1021_ = lean_ctor_get(v_s_1018_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v_s_1018_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_state_1021_);
lean_inc(v_importedEntries_1020_);
lean_dec(v_s_1018_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_state_1025_; lean_object* v___x_1027_; 
v_state_1025_ = lean_apply_2(v_addEntryFn_1019_, v_state_1021_, v_head_1017_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v_state_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_importedEntries_1020_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_state_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_1030_, lean_object* v_b_1031_){
_start:
{
if (lean_obj_tag(v_as_x27_1030_) == 0)
{
return v_b_1031_;
}
else
{
lean_object* v_head_1032_; lean_object* v_tail_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_head_1032_ = lean_ctor_get(v_as_x27_1030_, 0);
v_tail_1033_ = lean_ctor_get(v_as_x27_1030_, 1);
v___x_1034_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1035_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1036_ = lean_box(1);
v___x_1037_ = lean_box(0);
lean_inc_ref(v_b_1031_);
v___x_1038_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1035_, v___x_1034_, v_b_1031_, v___x_1036_, v___x_1037_);
v___x_1039_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_1038_, v_head_1032_);
lean_dec(v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v_toEnvExtension_1040_; lean_object* v_asyncMode_1041_; uint8_t v_logWrites_1042_; lean_object* v___f_1043_; uint8_t v___x_1044_; 
v_toEnvExtension_1040_ = lean_ctor_get(v___x_1034_, 0);
v_asyncMode_1041_ = lean_ctor_get(v_toEnvExtension_1040_, 2);
v_logWrites_1042_ = lean_ctor_get_uint8(v_toEnvExtension_1040_, sizeof(void*)*6);
lean_inc(v_head_1032_);
v___f_1043_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1043_, 0, v___x_1034_);
lean_closure_set(v___f_1043_, 1, v_head_1032_);
v___x_1044_ = 1;
if (v_logWrites_1042_ == 0)
{
lean_object* v___x_1045_; 
lean_inc_ref(v_toEnvExtension_1040_);
v___x_1045_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1040_, v_b_1031_, v___f_1043_, v_asyncMode_1041_, v___x_1037_, v___x_1044_);
v_as_x27_1030_ = v_tail_1033_;
v_b_1031_ = v___x_1045_;
goto _start;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref_n(v_toEnvExtension_1040_, 2);
v___x_1047_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1040_, v_b_1031_);
lean_dec_ref(v_b_1031_);
v___x_1048_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1040_, v___x_1047_, v___f_1043_, v_asyncMode_1041_, v___x_1037_, v___x_1044_);
v_as_x27_1030_ = v_tail_1033_;
v_b_1031_ = v___x_1048_;
goto _start;
}
}
else
{
v_as_x27_1030_ = v_tail_1033_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_1051_, lean_object* v_b_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_1051_, v_b_1052_);
lean_dec(v_as_x27_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_1054_, lean_object* v_dest_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1056_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1057_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1058_ = lean_box(1);
v___x_1059_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1056_, v___x_1057_, v_src_1054_, v___x_1058_);
v___x_1060_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_1059_, v_dest_1055_);
lean_dec(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_1061_, lean_object* v_as_x27_1062_, lean_object* v_b_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_1062_, v_b_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_1066_, lean_object* v_as_x27_1067_, lean_object* v_b_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_1066_, v_as_x27_1067_, v_b_1068_, v_a_1069_);
lean_dec(v_as_x27_1067_);
lean_dec(v_as_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1071_, lean_object* v_entry_1072_, lean_object* v_s_1073_){
_start:
{
lean_object* v_addEntryFn_1074_; lean_object* v_importedEntries_1075_; lean_object* v_state_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_addEntryFn_1074_ = lean_ctor_get(v___x_1071_, 3);
lean_inc(v_addEntryFn_1074_);
lean_dec_ref(v___x_1071_);
v_importedEntries_1075_ = lean_ctor_get(v_s_1073_, 0);
v_state_1076_ = lean_ctor_get(v_s_1073_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_s_1073_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_s_1073_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_state_1076_);
lean_inc(v_importedEntries_1075_);
lean_dec(v_s_1073_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_state_1080_; lean_object* v___x_1082_; 
v_state_1080_ = lean_apply_2(v_addEntryFn_1074_, v_state_1076_, v_entry_1072_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v_state_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_importedEntries_1075_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_state_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v___x_1085_, lean_object* v___f_1086_, lean_object* v___x_1087_, uint8_t v___x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_toEnvExtension_1090_; uint8_t v_logWrites_1091_; 
v_toEnvExtension_1090_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_toEnvExtension_1090_);
lean_dec_ref(v___x_1085_);
v_logWrites_1091_ = lean_ctor_get_uint8(v_toEnvExtension_1090_, sizeof(void*)*6);
if (v_logWrites_1091_ == 0)
{
lean_object* v_asyncMode_1092_; lean_object* v___x_1093_; 
v_asyncMode_1092_ = lean_ctor_get(v_toEnvExtension_1090_, 2);
lean_inc(v_asyncMode_1092_);
v___x_1093_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1090_, v_x_1089_, v___f_1086_, v_asyncMode_1092_, v___x_1087_, v___x_1088_);
lean_dec(v_asyncMode_1092_);
return v___x_1093_;
}
else
{
lean_object* v_asyncMode_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_asyncMode_1094_ = lean_ctor_get(v_toEnvExtension_1090_, 2);
lean_inc(v_asyncMode_1094_);
lean_inc_ref(v_toEnvExtension_1090_);
v___x_1095_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1090_, v_x_1089_);
lean_dec_ref(v_x_1089_);
v___x_1096_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1090_, v___x_1095_, v___f_1086_, v_asyncMode_1094_, v___x_1087_, v___x_1088_);
lean_dec(v_asyncMode_1094_);
return v___x_1096_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1085_ = stack[0].m_obj;
lean_object* v___f_1086_ = stack[1].m_obj;
lean_object* v___x_1087_ = stack[2].m_obj;
uint8_t v___x_1088_ = stack[3].m_num;
lean_object* v_x_1089_ = stack[4].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v___x_1085_, v___f_1086_, v___x_1087_, v___x_1088_, v_x_1089_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v___x_1098_, lean_object* v___f_1099_, lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v_x_1102_){
_start:
{
uint8_t v___x_579__boxed_1103_; lean_object* v_res_1104_; 
v___x_579__boxed_1103_ = lean_unbox(v___x_1101_);
v_res_1104_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v___x_1098_, v___f_1099_, v___x_1100_, v___x_579__boxed_1103_, v_x_1102_);
return v_res_1104_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__0));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__2));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__4));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__6));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__8));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5(lean_object* v_modifyEnv_1124_, lean_object* v___f_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_cls_1130_, lean_object* v_toBind_1131_, lean_object* v___f_1132_, lean_object* v_mod_1133_, lean_object* v_hint_1134_, uint8_t v_isMeta_1135_, uint8_t v_isExporting_1136_, uint8_t v_____do__lift_1137_){
_start:
{
lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1145_; lean_object* v___y_1146_; 
if (v_____do__lift_1137_ == 0)
{
lean_object* v___x_1158_; 
lean_dec(v_hint_1134_);
lean_dec(v_mod_1133_);
lean_dec(v___f_1132_);
lean_dec(v_toBind_1131_);
lean_dec(v_cls_1130_);
lean_dec(v_inst_1129_);
lean_dec_ref(v_inst_1128_);
lean_dec_ref(v_inst_1127_);
lean_dec_ref(v_inst_1126_);
v___x_1158_ = lean_apply_1(v_modifyEnv_1124_, v___f_1125_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___y_1161_; 
lean_dec_ref(v___f_1125_);
lean_dec(v_modifyEnv_1124_);
v___x_1159_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__7);
if (v_isExporting_1136_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__12));
v___y_1161_ = v___x_1168_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1169_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__13));
v___y_1161_ = v___x_1169_;
goto v___jp_1160_;
}
v___jp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_inc_ref(v___y_1161_);
v___x_1162_ = l_Lean_stringToMessageData(v___y_1161_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1159_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__9);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
if (v_isMeta_1135_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__10));
v___y_1145_ = v___x_1165_;
v___y_1146_ = v___x_1166_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__11));
v___y_1145_ = v___x_1165_;
v___y_1146_ = v___x_1167_;
goto v___jp_1144_;
}
}
}
v___jp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1139_);
lean_ctor_set(v___x_1141_, 1, v___y_1140_);
v___x_1142_ = l_Lean_addTrace___redArg(v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_cls_1130_, v___x_1141_);
v___x_1143_ = lean_apply_4(v_toBind_1131_, lean_box(0), lean_box(0), v___x_1142_, v___f_1132_);
return v___x_1143_;
}
v___jp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
lean_inc_ref(v___y_1146_);
v___x_1147_ = l_Lean_stringToMessageData(v___y_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1145_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__1);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_ofName(v_mod_1133_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_Name_isAnonymous(v_hint_1134_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__3);
v___x_1155_ = l_Lean_MessageData_ofName(v_hint_1134_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___y_1139_ = v___x_1152_;
v___y_1140_ = v___x_1156_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_hint_1134_);
v___x_1157_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___closed__5);
v___y_1139_ = v___x_1152_;
v___y_1140_ = v___x_1157_;
goto v___jp_1138_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifyEnv_1124_ = stack[0].m_obj;
lean_object* v___f_1125_ = stack[1].m_obj;
lean_object* v_inst_1126_ = stack[2].m_obj;
lean_object* v_inst_1127_ = stack[3].m_obj;
lean_object* v_inst_1128_ = stack[4].m_obj;
lean_object* v_inst_1129_ = stack[5].m_obj;
lean_object* v_cls_1130_ = stack[6].m_obj;
lean_object* v_toBind_1131_ = stack[7].m_obj;
lean_object* v___f_1132_ = stack[8].m_obj;
lean_object* v_mod_1133_ = stack[9].m_obj;
lean_object* v_hint_1134_ = stack[10].m_obj;
uint8_t v_isMeta_1135_ = stack[11].m_num;
uint8_t v_isExporting_1136_ = stack[12].m_num;
uint8_t v_____do__lift_1137_ = stack[13].m_num;
lean_object* v_res_1170_;
v_res_1170_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5(v_modifyEnv_1124_, v___f_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_cls_1130_, v_toBind_1131_, v___f_1132_, v_mod_1133_, v_hint_1134_, v_isMeta_1135_, v_isExporting_1136_, v_____do__lift_1137_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___boxed(lean_object* v_modifyEnv_1171_, lean_object* v___f_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_cls_1177_, lean_object* v_toBind_1178_, lean_object* v___f_1179_, lean_object* v_mod_1180_, lean_object* v_hint_1181_, lean_object* v_isMeta_1182_, lean_object* v_isExporting_1183_, lean_object* v_____do__lift_1184_){
_start:
{
uint8_t v_isMeta_boxed_1185_; uint8_t v_isExporting_boxed_1186_; uint8_t v_____do__lift_655__boxed_1187_; lean_object* v_res_1188_; 
v_isMeta_boxed_1185_ = lean_unbox(v_isMeta_1182_);
v_isExporting_boxed_1186_ = lean_unbox(v_isExporting_1183_);
v_____do__lift_655__boxed_1187_ = lean_unbox(v_____do__lift_1184_);
v_res_1188_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5(v_modifyEnv_1171_, v___f_1172_, v_inst_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_cls_1177_, v_toBind_1178_, v___f_1179_, v_mod_1180_, v_hint_1181_, v_isMeta_boxed_1185_, v_isExporting_boxed_1186_, v_____do__lift_655__boxed_1187_);
return v_res_1188_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v___x_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_entry_1192_, lean_object* v_inst_1193_, lean_object* v_modifyEnv_1194_, lean_object* v_inst_1195_, lean_object* v_toPure_1196_, lean_object* v_toBind_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_mod_1201_, lean_object* v_hint_1202_, uint8_t v_isMeta_1203_, uint8_t v_isExporting_1204_, lean_object* v_____do__lift_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1206_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1207_ = lean_box(1);
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1189_, v___x_1206_, v_____do__lift_1205_, v___x_1207_, v___x_1208_);
lean_inc_ref(v_entry_1192_);
v___x_1210_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1190_, v___x_1191_, v___x_1209_, v_entry_1192_);
if (v___x_1210_ == 0)
{
lean_object* v_getInheritedTraceOptions_1211_; lean_object* v___f_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v_cls_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_getInheritedTraceOptions_1211_ = lean_ctor_get(v_inst_1193_, 2);
lean_inc(v_getInheritedTraceOptions_1211_);
v___f_1212_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1212_, 0, v___x_1206_);
lean_closure_set(v___f_1212_, 1, v_entry_1192_);
v___x_1213_ = 1;
v___x_1214_ = lean_box(v___x_1213_);
v___f_1215_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1215_, 0, v___x_1206_);
lean_closure_set(v___f_1215_, 1, v___f_1212_);
lean_closure_set(v___f_1215_, 2, v___x_1208_);
lean_closure_set(v___f_1215_, 3, v___x_1214_);
lean_inc_ref(v___f_1215_);
lean_inc(v_modifyEnv_1194_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1216_, 0, v_modifyEnv_1194_);
lean_closure_set(v___f_1216_, 1, v___f_1215_);
v_cls_1217_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__6___closed__1));
lean_inc_n(v_toBind_1197_, 3);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1218_, 0, v_inst_1195_);
lean_closure_set(v___f_1218_, 1, v_toPure_1196_);
lean_closure_set(v___f_1218_, 2, v_cls_1217_);
lean_closure_set(v___f_1218_, 3, v_toBind_1197_);
v___x_1219_ = lean_box(v_isMeta_1203_);
v___x_1220_ = lean_box(v_isExporting_1204_);
v___f_1221_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1221_, 0, v_modifyEnv_1194_);
lean_closure_set(v___f_1221_, 1, v___f_1215_);
lean_closure_set(v___f_1221_, 2, v_inst_1198_);
lean_closure_set(v___f_1221_, 3, v_inst_1193_);
lean_closure_set(v___f_1221_, 4, v_inst_1199_);
lean_closure_set(v___f_1221_, 5, v_inst_1200_);
lean_closure_set(v___f_1221_, 6, v_cls_1217_);
lean_closure_set(v___f_1221_, 7, v_toBind_1197_);
lean_closure_set(v___f_1221_, 8, v___f_1216_);
lean_closure_set(v___f_1221_, 9, v_mod_1201_);
lean_closure_set(v___f_1221_, 10, v_hint_1202_);
lean_closure_set(v___f_1221_, 11, v___x_1219_);
lean_closure_set(v___f_1221_, 12, v___x_1220_);
v___x_1222_ = lean_apply_4(v_toBind_1197_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1211_, v___f_1218_);
v___x_1223_ = lean_apply_4(v_toBind_1197_, lean_box(0), lean_box(0), v___x_1222_, v___f_1221_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v_hint_1202_);
lean_dec(v_mod_1201_);
lean_dec(v_inst_1200_);
lean_dec_ref(v_inst_1199_);
lean_dec_ref(v_inst_1198_);
lean_dec(v_toBind_1197_);
lean_dec_ref(v_inst_1195_);
lean_dec(v_modifyEnv_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec_ref(v_entry_1192_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_apply_2(v_toPure_1196_, lean_box(0), v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1189_ = stack[0].m_obj;
lean_object* v___x_1190_ = stack[1].m_obj;
lean_object* v___x_1191_ = stack[2].m_obj;
lean_object* v_entry_1192_ = stack[3].m_obj;
lean_object* v_inst_1193_ = stack[4].m_obj;
lean_object* v_modifyEnv_1194_ = stack[5].m_obj;
lean_object* v_inst_1195_ = stack[6].m_obj;
lean_object* v_toPure_1196_ = stack[7].m_obj;
lean_object* v_toBind_1197_ = stack[8].m_obj;
lean_object* v_inst_1198_ = stack[9].m_obj;
lean_object* v_inst_1199_ = stack[10].m_obj;
lean_object* v_inst_1200_ = stack[11].m_obj;
lean_object* v_mod_1201_ = stack[12].m_obj;
lean_object* v_hint_1202_ = stack[13].m_obj;
uint8_t v_isMeta_1203_ = stack[14].m_num;
uint8_t v_isExporting_1204_ = stack[15].m_num;
lean_object* v_____do__lift_1205_ = stack[16].m_obj;
lean_object* v_res_1226_;
v_res_1226_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v___x_1189_, v___x_1190_, v___x_1191_, v_entry_1192_, v_inst_1193_, v_modifyEnv_1194_, v_inst_1195_, v_toPure_1196_, v_toBind_1197_, v_inst_1198_, v_inst_1199_, v_inst_1200_, v_mod_1201_, v_hint_1202_, v_isMeta_1203_, v_isExporting_1204_, v_____do__lift_1205_);
stack->m_obj
 = v_res_1226_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_1227_ = _args[0];
lean_object* v___x_1228_ = _args[1];
lean_object* v___x_1229_ = _args[2];
lean_object* v_entry_1230_ = _args[3];
lean_object* v_inst_1231_ = _args[4];
lean_object* v_modifyEnv_1232_ = _args[5];
lean_object* v_inst_1233_ = _args[6];
lean_object* v_toPure_1234_ = _args[7];
lean_object* v_toBind_1235_ = _args[8];
lean_object* v_inst_1236_ = _args[9];
lean_object* v_inst_1237_ = _args[10];
lean_object* v_inst_1238_ = _args[11];
lean_object* v_mod_1239_ = _args[12];
lean_object* v_hint_1240_ = _args[13];
lean_object* v_isMeta_1241_ = _args[14];
lean_object* v_isExporting_1242_ = _args[15];
lean_object* v_____do__lift_1243_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1244_; uint8_t v_isExporting_boxed_1245_; lean_object* v_res_1246_; 
v_isMeta_boxed_1244_ = lean_unbox(v_isMeta_1241_);
v_isExporting_boxed_1245_ = lean_unbox(v_isExporting_1242_);
v_res_1246_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v___x_1227_, v___x_1228_, v___x_1229_, v_entry_1230_, v_inst_1231_, v_modifyEnv_1232_, v_inst_1233_, v_toPure_1234_, v_toBind_1235_, v_inst_1236_, v_inst_1237_, v_inst_1238_, v_mod_1239_, v_hint_1240_, v_isMeta_boxed_1244_, v_isExporting_boxed_1245_, v_____do__lift_1243_);
return v_res_1246_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(lean_object* v_mod_1247_, uint8_t v_isMeta_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v___x_1251_, lean_object* v_inst_1252_, lean_object* v_modifyEnv_1253_, lean_object* v_inst_1254_, lean_object* v_toPure_1255_, lean_object* v_toBind_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_hint_1260_, lean_object* v_getEnv_1261_, lean_object* v_____do__lift_1262_){
_start:
{
uint8_t v_isExporting_1263_; lean_object* v_entry_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; 
v_isExporting_1263_ = lean_ctor_get_uint8(v_____do__lift_1262_, sizeof(void*)*13);
lean_inc(v_mod_1247_);
v_entry_1264_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1264_, 0, v_mod_1247_);
lean_ctor_set_uint8(v_entry_1264_, sizeof(void*)*1, v_isExporting_1263_);
lean_ctor_set_uint8(v_entry_1264_, sizeof(void*)*1 + 1, v_isMeta_1248_);
v___x_1265_ = lean_box(v_isMeta_1248_);
v___x_1266_ = lean_box(v_isExporting_1263_);
lean_inc(v_toBind_1256_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_1267_, 0, v___x_1249_);
lean_closure_set(v___f_1267_, 1, v___x_1250_);
lean_closure_set(v___f_1267_, 2, v___x_1251_);
lean_closure_set(v___f_1267_, 3, v_entry_1264_);
lean_closure_set(v___f_1267_, 4, v_inst_1252_);
lean_closure_set(v___f_1267_, 5, v_modifyEnv_1253_);
lean_closure_set(v___f_1267_, 6, v_inst_1254_);
lean_closure_set(v___f_1267_, 7, v_toPure_1255_);
lean_closure_set(v___f_1267_, 8, v_toBind_1256_);
lean_closure_set(v___f_1267_, 9, v_inst_1257_);
lean_closure_set(v___f_1267_, 10, v_inst_1258_);
lean_closure_set(v___f_1267_, 11, v_inst_1259_);
lean_closure_set(v___f_1267_, 12, v_mod_1247_);
lean_closure_set(v___f_1267_, 13, v_hint_1260_);
lean_closure_set(v___f_1267_, 14, v___x_1265_);
lean_closure_set(v___f_1267_, 15, v___x_1266_);
v___x_1268_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v_getEnv_1261_, v___f_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1247_ = stack[0].m_obj;
uint8_t v_isMeta_1248_ = stack[1].m_num;
lean_object* v___x_1249_ = stack[2].m_obj;
lean_object* v___x_1250_ = stack[3].m_obj;
lean_object* v___x_1251_ = stack[4].m_obj;
lean_object* v_inst_1252_ = stack[5].m_obj;
lean_object* v_modifyEnv_1253_ = stack[6].m_obj;
lean_object* v_inst_1254_ = stack[7].m_obj;
lean_object* v_toPure_1255_ = stack[8].m_obj;
lean_object* v_toBind_1256_ = stack[9].m_obj;
lean_object* v_inst_1257_ = stack[10].m_obj;
lean_object* v_inst_1258_ = stack[11].m_obj;
lean_object* v_inst_1259_ = stack[12].m_obj;
lean_object* v_hint_1260_ = stack[13].m_obj;
lean_object* v_getEnv_1261_ = stack[14].m_obj;
lean_object* v_____do__lift_1262_ = stack[15].m_obj;
lean_object* v_res_1269_;
v_res_1269_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(v_mod_1247_, v_isMeta_1248_, v___x_1249_, v___x_1250_, v___x_1251_, v_inst_1252_, v_modifyEnv_1253_, v_inst_1254_, v_toPure_1255_, v_toBind_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_hint_1260_, v_getEnv_1261_, v_____do__lift_1262_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed(lean_object* v_mod_1270_, lean_object* v_isMeta_1271_, lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v_inst_1275_, lean_object* v_modifyEnv_1276_, lean_object* v_inst_1277_, lean_object* v_toPure_1278_, lean_object* v_toBind_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_hint_1283_, lean_object* v_getEnv_1284_, lean_object* v_____do__lift_1285_){
_start:
{
uint8_t v_isMeta_boxed_1286_; lean_object* v_res_1287_; 
v_isMeta_boxed_1286_ = lean_unbox(v_isMeta_1271_);
v_res_1287_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(v_mod_1270_, v_isMeta_boxed_1286_, v___x_1272_, v___x_1273_, v___x_1274_, v_inst_1275_, v_modifyEnv_1276_, v_inst_1277_, v_toPure_1278_, v_toBind_1279_, v_inst_1280_, v_inst_1281_, v_inst_1282_, v_hint_1283_, v_getEnv_1284_, v_____do__lift_1285_);
lean_dec_ref(v_____do__lift_1285_);
return v_res_1287_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_mod_1294_, uint8_t v_isMeta_1295_, lean_object* v_hint_1296_){
_start:
{
lean_object* v_toApplicative_1297_; lean_object* v_toBind_1298_; lean_object* v_getEnv_1299_; lean_object* v_modifyEnv_1300_; lean_object* v_toPure_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; 
v_toApplicative_1297_ = lean_ctor_get(v_inst_1288_, 0);
v_toBind_1298_ = lean_ctor_get(v_inst_1288_, 1);
lean_inc_n(v_toBind_1298_, 2);
v_getEnv_1299_ = lean_ctor_get(v_inst_1289_, 0);
lean_inc_n(v_getEnv_1299_, 2);
v_modifyEnv_1300_ = lean_ctor_get(v_inst_1289_, 1);
lean_inc(v_modifyEnv_1300_);
lean_dec_ref(v_inst_1289_);
v_toPure_1301_ = lean_ctor_get(v_toApplicative_1297_, 1);
lean_inc(v_toPure_1301_);
v___x_1302_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1303_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1304_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1305_ = lean_box(v_isMeta_1295_);
v___f_1306_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_1306_, 0, v_mod_1294_);
lean_closure_set(v___f_1306_, 1, v___x_1305_);
lean_closure_set(v___f_1306_, 2, v___x_1304_);
lean_closure_set(v___f_1306_, 3, v___x_1302_);
lean_closure_set(v___f_1306_, 4, v___x_1303_);
lean_closure_set(v___f_1306_, 5, v_inst_1290_);
lean_closure_set(v___f_1306_, 6, v_modifyEnv_1300_);
lean_closure_set(v___f_1306_, 7, v_inst_1291_);
lean_closure_set(v___f_1306_, 8, v_toPure_1301_);
lean_closure_set(v___f_1306_, 9, v_toBind_1298_);
lean_closure_set(v___f_1306_, 10, v_inst_1288_);
lean_closure_set(v___f_1306_, 11, v_inst_1292_);
lean_closure_set(v___f_1306_, 12, v_inst_1293_);
lean_closure_set(v___f_1306_, 13, v_hint_1296_);
lean_closure_set(v___f_1306_, 14, v_getEnv_1299_);
v___x_1307_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v_getEnv_1299_, v___f_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1288_ = stack[0].m_obj;
lean_object* v_inst_1289_ = stack[1].m_obj;
lean_object* v_inst_1290_ = stack[2].m_obj;
lean_object* v_inst_1291_ = stack[3].m_obj;
lean_object* v_inst_1292_ = stack[4].m_obj;
lean_object* v_inst_1293_ = stack[5].m_obj;
lean_object* v_mod_1294_ = stack[6].m_obj;
uint8_t v_isMeta_1295_ = stack[7].m_num;
lean_object* v_hint_1296_ = stack[8].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v_inst_1293_, v_mod_1294_, v_isMeta_1295_, v_hint_1296_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_mod_1315_, lean_object* v_isMeta_1316_, lean_object* v_hint_1317_){
_start:
{
uint8_t v_isMeta_boxed_1318_; lean_object* v_res_1319_; 
v_isMeta_boxed_1318_ = lean_unbox(v_isMeta_1316_);
v_res_1319_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1309_, v_inst_1310_, v_inst_1311_, v_inst_1312_, v_inst_1313_, v_inst_1314_, v_mod_1315_, v_isMeta_boxed_1318_, v_hint_1317_);
return v_res_1319_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_mod_1327_, uint8_t v_isMeta_1328_, lean_object* v_hint_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_mod_1327_, v_isMeta_1328_, v_hint_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1321_ = stack[1].m_obj;
lean_object* v_inst_1322_ = stack[2].m_obj;
lean_object* v_inst_1323_ = stack[3].m_obj;
lean_object* v_inst_1324_ = stack[4].m_obj;
lean_object* v_inst_1325_ = stack[5].m_obj;
lean_object* v_inst_1326_ = stack[6].m_obj;
lean_object* v_mod_1327_ = stack[7].m_obj;
uint8_t v_isMeta_1328_ = stack[8].m_num;
lean_object* v_hint_1329_ = stack[9].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_box(0), v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_mod_1327_, v_isMeta_1328_, v_hint_1329_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_mod_1339_, lean_object* v_isMeta_1340_, lean_object* v_hint_1341_){
_start:
{
uint8_t v_isMeta_boxed_1342_; lean_object* v_res_1343_; 
v_isMeta_boxed_1342_ = lean_unbox(v_isMeta_1340_);
v_res_1343_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_mod_1339_, v_isMeta_boxed_1342_, v_hint_1341_);
return v_res_1343_;
}
}
lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, uint8_t v_isMeta_1351_, lean_object* v_toPure_1352_, lean_object* v_____do__lift_1353_){
_start:
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = l_Lean_Environment_mainModule(v_____do__lift_1353_);
v___x_1355_ = lean_name_eq(v_modName_1344_, v___x_1354_);
lean_dec(v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_toPure_1352_);
v___x_1356_ = lean_box(0);
v___x_1357_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_modName_1344_, v_isMeta_1351_, v___x_1356_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v_inst_1350_);
lean_dec_ref(v_inst_1349_);
lean_dec_ref(v_inst_1348_);
lean_dec_ref(v_inst_1347_);
lean_dec_ref(v_inst_1346_);
lean_dec_ref(v_inst_1345_);
lean_dec(v_modName_1344_);
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_apply_2(v_toPure_1352_, lean_box(0), v___x_1358_);
return v___x_1359_;
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUse___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_modName_1344_ = stack[0].m_obj;
lean_object* v_inst_1345_ = stack[1].m_obj;
lean_object* v_inst_1346_ = stack[2].m_obj;
lean_object* v_inst_1347_ = stack[3].m_obj;
lean_object* v_inst_1348_ = stack[4].m_obj;
lean_object* v_inst_1349_ = stack[5].m_obj;
lean_object* v_inst_1350_ = stack[6].m_obj;
uint8_t v_isMeta_1351_ = stack[7].m_num;
lean_object* v_toPure_1352_ = stack[8].m_obj;
lean_object* v_____do__lift_1353_ = stack[9].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_isMeta_1351_, v_toPure_1352_, v_____do__lift_1353_);
stack->m_obj
 = v_res_1360_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_isMeta_1368_, lean_object* v_toPure_1369_, lean_object* v_____do__lift_1370_){
_start:
{
uint8_t v_isMeta_boxed_1371_; lean_object* v_res_1372_; 
v_isMeta_boxed_1371_ = lean_unbox(v_isMeta_1368_);
v_res_1372_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1361_, v_inst_1362_, v_inst_1363_, v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_isMeta_boxed_1371_, v_toPure_1369_, v_____do__lift_1370_);
lean_dec_ref(v_____do__lift_1370_);
return v_res_1372_;
}
}
lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_modName_1379_, uint8_t v_isMeta_1380_){
_start:
{
lean_object* v_toApplicative_1381_; lean_object* v_toBind_1382_; lean_object* v_getEnv_1383_; lean_object* v_toPure_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v_toApplicative_1381_ = lean_ctor_get(v_inst_1373_, 0);
v_toBind_1382_ = lean_ctor_get(v_inst_1373_, 1);
lean_inc(v_toBind_1382_);
v_getEnv_1383_ = lean_ctor_get(v_inst_1374_, 0);
lean_inc(v_getEnv_1383_);
v_toPure_1384_ = lean_ctor_get(v_toApplicative_1381_, 1);
lean_inc(v_toPure_1384_);
v___x_1385_ = lean_box(v_isMeta_1380_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1386_, 0, v_modName_1379_);
lean_closure_set(v___f_1386_, 1, v_inst_1373_);
lean_closure_set(v___f_1386_, 2, v_inst_1374_);
lean_closure_set(v___f_1386_, 3, v_inst_1375_);
lean_closure_set(v___f_1386_, 4, v_inst_1376_);
lean_closure_set(v___f_1386_, 5, v_inst_1377_);
lean_closure_set(v___f_1386_, 6, v_inst_1378_);
lean_closure_set(v___f_1386_, 7, v___x_1385_);
lean_closure_set(v___f_1386_, 8, v_toPure_1384_);
v___x_1387_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v_getEnv_1383_, v___f_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT void l_Lean_recordExtraModUse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1373_ = stack[0].m_obj;
lean_object* v_inst_1374_ = stack[1].m_obj;
lean_object* v_inst_1375_ = stack[2].m_obj;
lean_object* v_inst_1376_ = stack[3].m_obj;
lean_object* v_inst_1377_ = stack[4].m_obj;
lean_object* v_inst_1378_ = stack[5].m_obj;
lean_object* v_modName_1379_ = stack[6].m_obj;
uint8_t v_isMeta_1380_ = stack[7].m_num;
lean_object* v_res_1388_;
v_res_1388_ = l_Lean_recordExtraModUse___redArg(v_inst_1373_, v_inst_1374_, v_inst_1375_, v_inst_1376_, v_inst_1377_, v_inst_1378_, v_modName_1379_, v_isMeta_1380_);
stack->m_obj
 = v_res_1388_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_modName_1395_, lean_object* v_isMeta_1396_){
_start:
{
uint8_t v_isMeta_boxed_1397_; lean_object* v_res_1398_; 
v_isMeta_boxed_1397_ = lean_unbox(v_isMeta_1396_);
v_res_1398_ = l_Lean_recordExtraModUse___redArg(v_inst_1389_, v_inst_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_modName_1395_, v_isMeta_boxed_1397_);
return v_res_1398_;
}
}
lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_modName_1406_, uint8_t v_isMeta_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_recordExtraModUse___redArg(v_inst_1400_, v_inst_1401_, v_inst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_modName_1406_, v_isMeta_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT void l_Lean_recordExtraModUse_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1400_ = stack[1].m_obj;
lean_object* v_inst_1401_ = stack[2].m_obj;
lean_object* v_inst_1402_ = stack[3].m_obj;
lean_object* v_inst_1403_ = stack[4].m_obj;
lean_object* v_inst_1404_ = stack[5].m_obj;
lean_object* v_inst_1405_ = stack[6].m_obj;
lean_object* v_modName_1406_ = stack[7].m_obj;
uint8_t v_isMeta_1407_ = stack[8].m_num;
lean_object* v_res_1409_;
v_res_1409_ = l_Lean_recordExtraModUse(lean_box(0), v_inst_1400_, v_inst_1401_, v_inst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_modName_1406_, v_isMeta_1407_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_modName_1417_, lean_object* v_isMeta_1418_){
_start:
{
uint8_t v_isMeta_boxed_1419_; lean_object* v_res_1420_; 
v_isMeta_boxed_1419_ = lean_unbox(v_isMeta_1418_);
v_res_1420_ = l_Lean_recordExtraModUse(v_m_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v_inst_1414_, v_inst_1415_, v_inst_1416_, v_modName_1417_, v_isMeta_boxed_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1421_, lean_object* v_____s_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_apply_2(v_toPure_1421_, lean_box(0), v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1425_, lean_object* v_toPure_1426_, lean_object* v_r_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1425_);
v___x_1429_ = lean_apply_2(v_toPure_1426_, lean_box(0), v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1430_, lean_object* v___x_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_declName_1438_, lean_object* v_toBind_1439_, lean_object* v___f_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v_modules_1445_; lean_object* v___x_1446_; lean_object* v_toImport_1447_; lean_object* v_module_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1444_ = l_Lean_Environment_header(v_env_1430_);
v_modules_1445_ = lean_ctor_get(v___x_1444_, 3);
lean_inc_ref(v_modules_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = lean_array_get(v___x_1431_, v_modules_1445_, v_a_1441_);
lean_dec_ref(v_modules_1445_);
v_toImport_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_toImport_1447_);
lean_dec(v___x_1446_);
v_module_1448_ = lean_ctor_get(v_toImport_1447_, 0);
lean_inc(v_module_1448_);
lean_dec_ref(v_toImport_1447_);
v___x_1449_ = 0;
v___x_1450_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1432_, v_inst_1433_, v_inst_1434_, v_inst_1435_, v_inst_1436_, v_inst_1437_, v_module_1448_, v___x_1449_, v_declName_1438_);
v___x_1451_ = lean_apply_4(v_toBind_1439_, lean_box(0), lean_box(0), v___x_1450_, v___f_1440_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1452_, lean_object* v___x_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_declName_1460_, lean_object* v_toBind_1461_, lean_object* v___f_1462_, lean_object* v_a_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1452_, v___x_1453_, v_inst_1454_, v_inst_1455_, v_inst_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_declName_1460_, v_toBind_1461_, v___f_1462_, v_a_1463_, v_x_1464_, v___y_1465_);
lean_dec(v_a_1463_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_env_1452_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1467_, lean_object* v_env_1468_, lean_object* v___x_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_declName_1476_, lean_object* v_toBind_1477_, lean_object* v___f_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v_____r_1482_){
_start:
{
lean_object* v___y_1484_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1492_ = l_Lean_indirectModUseExt;
v___x_1493_ = lean_box(1);
v___x_1494_ = lean_box(0);
lean_inc_ref(v_env_1468_);
v___x_1495_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1479_, v___x_1492_, v_env_1468_, v___x_1493_, v___x_1494_);
lean_inc(v_declName_1476_);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1480_, v___x_1481_, v___x_1495_, v_declName_1476_);
lean_dec(v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1484_ = v___x_1497_;
goto v___jp_1483_;
}
else
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1496_, 1);
v___y_1484_ = v_val_1498_;
goto v___jp_1483_;
}
v___jp_1483_:
{
lean_object* v___x_1485_; lean_object* v___f_1486_; lean_object* v___f_1487_; size_t v_sz_1488_; size_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1485_ = lean_box(0);
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1486_, 0, v___x_1485_);
lean_closure_set(v___f_1486_, 1, v_toPure_1467_);
lean_inc(v_toBind_1477_);
lean_inc_ref(v_inst_1470_);
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1487_, 0, v_env_1468_);
lean_closure_set(v___f_1487_, 1, v___x_1469_);
lean_closure_set(v___f_1487_, 2, v_inst_1470_);
lean_closure_set(v___f_1487_, 3, v_inst_1471_);
lean_closure_set(v___f_1487_, 4, v_inst_1472_);
lean_closure_set(v___f_1487_, 5, v_inst_1473_);
lean_closure_set(v___f_1487_, 6, v_inst_1474_);
lean_closure_set(v___f_1487_, 7, v_inst_1475_);
lean_closure_set(v___f_1487_, 8, v_declName_1476_);
lean_closure_set(v___f_1487_, 9, v_toBind_1477_);
lean_closure_set(v___f_1487_, 10, v___f_1486_);
v_sz_1488_ = lean_array_size(v___y_1484_);
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1470_, v___y_1484_, v___f_1487_, v_sz_1488_, v___x_1489_, v___x_1485_);
v___x_1491_ = lean_apply_4(v_toBind_1477_, lean_box(0), lean_box(0), v___x_1490_, v___f_1478_);
return v___x_1491_;
}
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_declName_1506_, lean_object* v_toBind_1507_, lean_object* v___f_1508_, uint8_t v_isMeta_1509_, lean_object* v_____do__lift_1510_){
_start:
{
uint8_t v___y_1512_; 
if (v_isMeta_1509_ == 0)
{
lean_dec_ref(v_____do__lift_1510_);
v___y_1512_ = v_isMeta_1509_;
goto v___jp_1511_;
}
else
{
uint8_t v___x_1517_; 
lean_inc(v_declName_1506_);
v___x_1517_ = l_Lean_isMarkedMeta(v_____do__lift_1510_, v_declName_1506_);
if (v___x_1517_ == 0)
{
v___y_1512_ = v_isMeta_1509_;
goto v___jp_1511_;
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
v___y_1512_ = v___x_1518_;
goto v___jp_1511_;
}
}
v___jp_1511_:
{
lean_object* v_toImport_1513_; lean_object* v_module_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_toImport_1513_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_toImport_1513_);
lean_dec_ref(v___x_1499_);
v_module_1514_ = lean_ctor_get(v_toImport_1513_, 0);
lean_inc(v_module_1514_);
lean_dec_ref(v_toImport_1513_);
v___x_1515_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_module_1514_, v___y_1512_, v_declName_1506_);
v___x_1516_ = lean_apply_4(v_toBind_1507_, lean_box(0), lean_box(0), v___x_1515_, v___f_1508_);
return v___x_1516_;
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1499_ = stack[0].m_obj;
lean_object* v_inst_1500_ = stack[1].m_obj;
lean_object* v_inst_1501_ = stack[2].m_obj;
lean_object* v_inst_1502_ = stack[3].m_obj;
lean_object* v_inst_1503_ = stack[4].m_obj;
lean_object* v_inst_1504_ = stack[5].m_obj;
lean_object* v_inst_1505_ = stack[6].m_obj;
lean_object* v_declName_1506_ = stack[7].m_obj;
lean_object* v_toBind_1507_ = stack[8].m_obj;
lean_object* v___f_1508_ = stack[9].m_obj;
uint8_t v_isMeta_1509_ = stack[10].m_num;
lean_object* v_____do__lift_1510_ = stack[11].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_declName_1506_, v_toBind_1507_, v___f_1508_, v_isMeta_1509_, v_____do__lift_1510_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_declName_1527_, lean_object* v_toBind_1528_, lean_object* v___f_1529_, lean_object* v_isMeta_1530_, lean_object* v_____do__lift_1531_){
_start:
{
uint8_t v_isMeta_boxed_1532_; lean_object* v_res_1533_; 
v_isMeta_boxed_1532_ = lean_unbox(v_isMeta_1530_);
v_res_1533_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_declName_1527_, v_toBind_1528_, v___f_1529_, v_isMeta_boxed_1532_, v_____do__lift_1531_);
return v_res_1533_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1534_, lean_object* v_declName_1535_, lean_object* v___x_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_toBind_1543_, lean_object* v___f_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v___x_1547_, uint8_t v_isMeta_1548_, lean_object* v_getEnv_1549_, lean_object* v_env_1550_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1550_, v_declName_1535_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref(v_env_1550_);
lean_dec(v_getEnv_1549_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
lean_dec(v___f_1544_);
lean_dec(v_toBind_1543_);
lean_dec(v_inst_1542_);
lean_dec_ref(v_inst_1541_);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec_ref(v_inst_1537_);
lean_dec_ref(v___x_1536_);
lean_dec(v_declName_1535_);
goto v___jp_1551_;
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1556_; lean_object* v_modules_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Environment_header(v_env_1550_);
v_modules_1557_ = lean_ctor_get(v___x_1556_, 3);
lean_inc_ref(v_modules_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = lean_array_get_size(v_modules_1557_);
v___x_1559_ = lean_nat_dec_lt(v_val_1555_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_dec_ref(v_modules_1557_);
lean_dec(v_val_1555_);
lean_dec_ref(v_env_1550_);
lean_dec(v_getEnv_1549_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
lean_dec(v___f_1544_);
lean_dec(v_toBind_1543_);
lean_dec(v_inst_1542_);
lean_dec_ref(v_inst_1541_);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec_ref(v_inst_1537_);
lean_dec_ref(v___x_1536_);
lean_dec(v_declName_1535_);
goto v___jp_1551_;
}
else
{
lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
lean_inc_n(v_toBind_1543_, 2);
lean_inc(v_declName_1535_);
lean_inc(v_inst_1542_);
lean_inc_ref(v_inst_1541_);
lean_inc_ref(v_inst_1540_);
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
lean_inc_ref(v_inst_1537_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1560_, 0, v_toPure_1534_);
lean_closure_set(v___f_1560_, 1, v_env_1550_);
lean_closure_set(v___f_1560_, 2, v___x_1536_);
lean_closure_set(v___f_1560_, 3, v_inst_1537_);
lean_closure_set(v___f_1560_, 4, v_inst_1538_);
lean_closure_set(v___f_1560_, 5, v_inst_1539_);
lean_closure_set(v___f_1560_, 6, v_inst_1540_);
lean_closure_set(v___f_1560_, 7, v_inst_1541_);
lean_closure_set(v___f_1560_, 8, v_inst_1542_);
lean_closure_set(v___f_1560_, 9, v_declName_1535_);
lean_closure_set(v___f_1560_, 10, v_toBind_1543_);
lean_closure_set(v___f_1560_, 11, v___f_1544_);
lean_closure_set(v___f_1560_, 12, v___x_1545_);
lean_closure_set(v___f_1560_, 13, v___x_1546_);
lean_closure_set(v___f_1560_, 14, v___x_1547_);
v___x_1561_ = lean_array_fget(v_modules_1557_, v_val_1555_);
lean_dec(v_val_1555_);
lean_dec_ref(v_modules_1557_);
v___x_1562_ = lean_box(v_isMeta_1548_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1563_, 0, v___x_1561_);
lean_closure_set(v___f_1563_, 1, v_inst_1537_);
lean_closure_set(v___f_1563_, 2, v_inst_1538_);
lean_closure_set(v___f_1563_, 3, v_inst_1539_);
lean_closure_set(v___f_1563_, 4, v_inst_1540_);
lean_closure_set(v___f_1563_, 5, v_inst_1541_);
lean_closure_set(v___f_1563_, 6, v_inst_1542_);
lean_closure_set(v___f_1563_, 7, v_declName_1535_);
lean_closure_set(v___f_1563_, 8, v_toBind_1543_);
lean_closure_set(v___f_1563_, 9, v___f_1560_);
lean_closure_set(v___f_1563_, 10, v___x_1562_);
v___x_1564_ = lean_apply_4(v_toBind_1543_, lean_box(0), lean_box(0), v_getEnv_1549_, v___f_1563_);
return v___x_1564_;
}
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_apply_2(v_toPure_1534_, lean_box(0), v___x_1552_);
return v___x_1553_;
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1534_ = stack[0].m_obj;
lean_object* v_declName_1535_ = stack[1].m_obj;
lean_object* v___x_1536_ = stack[2].m_obj;
lean_object* v_inst_1537_ = stack[3].m_obj;
lean_object* v_inst_1538_ = stack[4].m_obj;
lean_object* v_inst_1539_ = stack[5].m_obj;
lean_object* v_inst_1540_ = stack[6].m_obj;
lean_object* v_inst_1541_ = stack[7].m_obj;
lean_object* v_inst_1542_ = stack[8].m_obj;
lean_object* v_toBind_1543_ = stack[9].m_obj;
lean_object* v___f_1544_ = stack[10].m_obj;
lean_object* v___x_1545_ = stack[11].m_obj;
lean_object* v___x_1546_ = stack[12].m_obj;
lean_object* v___x_1547_ = stack[13].m_obj;
uint8_t v_isMeta_1548_ = stack[14].m_num;
lean_object* v_getEnv_1549_ = stack[15].m_obj;
lean_object* v_env_1550_ = stack[16].m_obj;
lean_object* v_res_1565_;
v_res_1565_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1534_, v_declName_1535_, v___x_1536_, v_inst_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, v_inst_1541_, v_inst_1542_, v_toBind_1543_, v___f_1544_, v___x_1545_, v___x_1546_, v___x_1547_, v_isMeta_1548_, v_getEnv_1549_, v_env_1550_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1566_ = _args[0];
lean_object* v_declName_1567_ = _args[1];
lean_object* v___x_1568_ = _args[2];
lean_object* v_inst_1569_ = _args[3];
lean_object* v_inst_1570_ = _args[4];
lean_object* v_inst_1571_ = _args[5];
lean_object* v_inst_1572_ = _args[6];
lean_object* v_inst_1573_ = _args[7];
lean_object* v_inst_1574_ = _args[8];
lean_object* v_toBind_1575_ = _args[9];
lean_object* v___f_1576_ = _args[10];
lean_object* v___x_1577_ = _args[11];
lean_object* v___x_1578_ = _args[12];
lean_object* v___x_1579_ = _args[13];
lean_object* v_isMeta_1580_ = _args[14];
lean_object* v_getEnv_1581_ = _args[15];
lean_object* v_env_1582_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1583_; lean_object* v_res_1584_; 
v_isMeta_boxed_1583_ = lean_unbox(v_isMeta_1580_);
v_res_1584_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1566_, v_declName_1567_, v___x_1568_, v_inst_1569_, v_inst_1570_, v_inst_1571_, v_inst_1572_, v_inst_1573_, v_inst_1574_, v_toBind_1575_, v___f_1576_, v___x_1577_, v___x_1578_, v___x_1579_, v_isMeta_boxed_1583_, v_getEnv_1581_, v_env_1582_);
return v_res_1584_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_declName_1593_, uint8_t v_isMeta_1594_){
_start:
{
lean_object* v_toApplicative_1595_; lean_object* v_toBind_1596_; lean_object* v_getEnv_1597_; lean_object* v_toPure_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; 
v_toApplicative_1595_ = lean_ctor_get(v_inst_1587_, 0);
v_toBind_1596_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1596_, 2);
v_getEnv_1597_ = lean_ctor_get(v_inst_1588_, 0);
lean_inc_n(v_getEnv_1597_, 2);
v_toPure_1598_ = lean_ctor_get(v_toApplicative_1595_, 1);
lean_inc_n(v_toPure_1598_, 2);
v___x_1599_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___redArg___closed__0));
v___x_1600_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___redArg___closed__1));
v___x_1601_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___x_1602_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1603_, 0, v_toPure_1598_);
v___x_1604_ = lean_box(v_isMeta_1594_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1605_, 0, v_toPure_1598_);
lean_closure_set(v___f_1605_, 1, v_declName_1593_);
lean_closure_set(v___f_1605_, 2, v___x_1602_);
lean_closure_set(v___f_1605_, 3, v_inst_1587_);
lean_closure_set(v___f_1605_, 4, v_inst_1588_);
lean_closure_set(v___f_1605_, 5, v_inst_1589_);
lean_closure_set(v___f_1605_, 6, v_inst_1590_);
lean_closure_set(v___f_1605_, 7, v_inst_1591_);
lean_closure_set(v___f_1605_, 8, v_inst_1592_);
lean_closure_set(v___f_1605_, 9, v_toBind_1596_);
lean_closure_set(v___f_1605_, 10, v___f_1603_);
lean_closure_set(v___f_1605_, 11, v___x_1601_);
lean_closure_set(v___f_1605_, 12, v___x_1599_);
lean_closure_set(v___f_1605_, 13, v___x_1600_);
lean_closure_set(v___f_1605_, 14, v___x_1604_);
lean_closure_set(v___f_1605_, 15, v_getEnv_1597_);
v___x_1606_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v_getEnv_1597_, v___f_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1587_ = stack[0].m_obj;
lean_object* v_inst_1588_ = stack[1].m_obj;
lean_object* v_inst_1589_ = stack[2].m_obj;
lean_object* v_inst_1590_ = stack[3].m_obj;
lean_object* v_inst_1591_ = stack[4].m_obj;
lean_object* v_inst_1592_ = stack[5].m_obj;
lean_object* v_declName_1593_ = stack[6].m_obj;
uint8_t v_isMeta_1594_ = stack[7].m_num;
lean_object* v_res_1607_;
v_res_1607_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1587_, v_inst_1588_, v_inst_1589_, v_inst_1590_, v_inst_1591_, v_inst_1592_, v_declName_1593_, v_isMeta_1594_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_declName_1614_, lean_object* v_isMeta_1615_){
_start:
{
uint8_t v_isMeta_boxed_1616_; lean_object* v_res_1617_; 
v_isMeta_boxed_1616_ = lean_unbox(v_isMeta_1615_);
v_res_1617_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1608_, v_inst_1609_, v_inst_1610_, v_inst_1611_, v_inst_1612_, v_inst_1613_, v_declName_1614_, v_isMeta_boxed_1616_);
return v_res_1617_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_declName_1625_, uint8_t v_isMeta_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1619_, v_inst_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_declName_1625_, v_isMeta_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1619_ = stack[1].m_obj;
lean_object* v_inst_1620_ = stack[2].m_obj;
lean_object* v_inst_1621_ = stack[3].m_obj;
lean_object* v_inst_1622_ = stack[4].m_obj;
lean_object* v_inst_1623_ = stack[5].m_obj;
lean_object* v_inst_1624_ = stack[6].m_obj;
lean_object* v_declName_1625_ = stack[7].m_obj;
uint8_t v_isMeta_1626_ = stack[8].m_num;
lean_object* v_res_1628_;
v_res_1628_ = l_Lean_recordExtraModUseFromDecl(lean_box(0), v_inst_1619_, v_inst_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_declName_1625_, v_isMeta_1626_);
stack->m_obj
 = v_res_1628_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_declName_1636_, lean_object* v_isMeta_1637_){
_start:
{
uint8_t v_isMeta_boxed_1638_; lean_object* v_res_1639_; 
v_isMeta_boxed_1638_ = lean_unbox(v_isMeta_1637_);
v_res_1639_ = l_Lean_recordExtraModUseFromDecl(v_m_1629_, v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_declName_1636_, v_isMeta_boxed_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1640_, lean_object* v_e_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_box(0);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1645_);
lean_dec_ref(v_x_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_mk(v_es_1647_);
return v___x_1648_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1666_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1667_;
v_res_1667_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1667_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1669_;
}
}
uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1673_, lean_object* v_modIdx_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1675_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1676_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1677_ = 0;
v___x_1678_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1675_, v___x_1676_, v_env_1673_, v_modIdx_1674_, v___x_1677_);
v___x_1679_ = lean_array_get_size(v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_nat_dec_eq(v___x_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
uint8_t v___x_1682_; 
v___x_1682_ = 1;
return v___x_1682_;
}
else
{
uint8_t v___x_1683_; 
v___x_1683_ = 0;
return v___x_1683_;
}
}
}
LEAN_EXPORT void l_Lean_isExtraRevModUse_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1673_ = stack[0].m_obj;
lean_object* v_modIdx_1674_ = stack[1].m_obj;
uint8_t v_res_1684_;
v_res_1684_ = l_Lean_isExtraRevModUse(v_env_1673_, v_modIdx_1674_);
stack->m_num = v_res_1684_;
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1685_, lean_object* v_modIdx_1686_){
_start:
{
uint8_t v_res_1687_; lean_object* v_r_1688_; 
v_res_1687_ = l_Lean_isExtraRevModUse(v_env_1685_, v_modIdx_1686_);
lean_dec(v_modIdx_1686_);
lean_dec_ref(v_env_1685_);
v_r_1688_ = lean_box(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1689_, lean_object* v___x_1690_, lean_object* v_s_1691_){
_start:
{
lean_object* v_addEntryFn_1692_; lean_object* v_importedEntries_1693_; lean_object* v_state_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_addEntryFn_1692_ = lean_ctor_get(v___x_1689_, 3);
lean_inc(v_addEntryFn_1692_);
lean_dec_ref(v___x_1689_);
v_importedEntries_1693_ = lean_ctor_get(v_s_1691_, 0);
v_state_1694_ = lean_ctor_get(v_s_1691_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_s_1691_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_s_1691_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_state_1694_);
lean_inc(v_importedEntries_1693_);
lean_dec(v_s_1691_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_state_1698_; lean_object* v___x_1700_; 
v_state_1698_ = lean_apply_2(v_addEntryFn_1692_, v_state_1694_, v___x_1690_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v_state_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_importedEntries_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_state_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object* v___x_1703_, uint8_t v___x_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_toEnvExtension_1706_; lean_object* v_asyncMode_1707_; uint8_t v_logWrites_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; 
v_toEnvExtension_1706_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_toEnvExtension_1706_);
v_asyncMode_1707_ = lean_ctor_get(v_toEnvExtension_1706_, 2);
lean_inc(v_asyncMode_1707_);
v_logWrites_1708_ = lean_ctor_get_uint8(v_toEnvExtension_1706_, sizeof(void*)*6);
v___x_1709_ = lean_box(0);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1710_, 0, v___x_1703_);
lean_closure_set(v___f_1710_, 1, v___x_1709_);
v___x_1711_ = lean_box(0);
if (v_logWrites_1708_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1706_, v_x_1705_, v___f_1710_, v_asyncMode_1707_, v___x_1711_, v___x_1704_);
lean_dec(v_asyncMode_1707_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_inc_ref(v_toEnvExtension_1706_);
v___x_1713_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1706_, v_x_1705_);
lean_dec_ref(v_x_1705_);
v___x_1714_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1706_, v___x_1713_, v___f_1710_, v_asyncMode_1707_, v___x_1711_, v___x_1704_);
lean_dec(v_asyncMode_1707_);
return v___x_1714_;
}
}
}
LEAN_EXPORT void l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1703_ = stack[0].m_obj;
uint8_t v___x_1704_ = stack[1].m_num;
lean_object* v_x_1705_ = stack[2].m_obj;
lean_object* v_res_1715_;
v_res_1715_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(v___x_1703_, v___x_1704_, v_x_1705_);
stack->m_obj
 = v_res_1715_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___boxed(lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v_x_1718_){
_start:
{
uint8_t v___x_217__boxed_1719_; lean_object* v_res_1720_; 
v___x_217__boxed_1719_ = lean_unbox(v___x_1717_);
v_res_1720_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(v___x_1716_, v___x_217__boxed_1719_, v_x_1718_);
return v_res_1720_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__0));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5(lean_object* v_modifyEnv_1724_, lean_object* v___f_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_cls_1730_, lean_object* v_toBind_1731_, lean_object* v___f_1732_, uint8_t v_____do__lift_1733_){
_start:
{
if (v_____do__lift_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v___f_1732_);
lean_dec(v_toBind_1731_);
lean_dec(v_cls_1730_);
lean_dec(v_inst_1729_);
lean_dec_ref(v_inst_1728_);
lean_dec_ref(v_inst_1727_);
lean_dec_ref(v_inst_1726_);
v___x_1734_ = lean_apply_1(v_modifyEnv_1724_, v___f_1725_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref(v___f_1725_);
lean_dec(v_modifyEnv_1724_);
v___x_1735_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___closed__1);
v___x_1736_ = l_Lean_addTrace___redArg(v_inst_1726_, v_inst_1727_, v_inst_1728_, v_inst_1729_, v_cls_1730_, v___x_1735_);
v___x_1737_ = lean_apply_4(v_toBind_1731_, lean_box(0), lean_box(0), v___x_1736_, v___f_1732_);
return v___x_1737_;
}
}
}
LEAN_EXPORT void l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifyEnv_1724_ = stack[0].m_obj;
lean_object* v___f_1725_ = stack[1].m_obj;
lean_object* v_inst_1726_ = stack[2].m_obj;
lean_object* v_inst_1727_ = stack[3].m_obj;
lean_object* v_inst_1728_ = stack[4].m_obj;
lean_object* v_inst_1729_ = stack[5].m_obj;
lean_object* v_cls_1730_ = stack[6].m_obj;
lean_object* v_toBind_1731_ = stack[7].m_obj;
lean_object* v___f_1732_ = stack[8].m_obj;
uint8_t v_____do__lift_1733_ = stack[9].m_num;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5(v_modifyEnv_1724_, v___f_1725_, v_inst_1726_, v_inst_1727_, v_inst_1728_, v_inst_1729_, v_cls_1730_, v_toBind_1731_, v___f_1732_, v_____do__lift_1733_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___boxed(lean_object* v_modifyEnv_1739_, lean_object* v___f_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_cls_1745_, lean_object* v_toBind_1746_, lean_object* v___f_1747_, lean_object* v_____do__lift_1748_){
_start:
{
uint8_t v_____do__lift_262__boxed_1749_; lean_object* v_res_1750_; 
v_____do__lift_262__boxed_1749_ = lean_unbox(v_____do__lift_1748_);
v_res_1750_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5(v_modifyEnv_1739_, v___f_1740_, v_inst_1741_, v_inst_1742_, v_inst_1743_, v_inst_1744_, v_cls_1745_, v_toBind_1746_, v___f_1747_, v_____do__lift_262__boxed_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v___x_1751_, lean_object* v_toPure_1752_, lean_object* v_inst_1753_, lean_object* v_modifyEnv_1754_, lean_object* v_inst_1755_, lean_object* v_toBind_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_____do__lift_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1761_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1762_ = lean_box(1);
v___x_1763_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1751_, v___x_1761_, v_____do__lift_1760_, v___x_1762_);
v___x_1764_ = l_List_isEmpty___redArg(v___x_1763_);
lean_dec(v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v_inst_1759_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
lean_dec(v_toBind_1756_);
lean_dec_ref(v_inst_1755_);
lean_dec(v_modifyEnv_1754_);
lean_dec_ref(v_inst_1753_);
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_apply_2(v_toPure_1752_, lean_box(0), v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v_getInheritedTraceOptions_1767_; lean_object* v___x_1768_; lean_object* v___f_1769_; lean_object* v___f_1770_; lean_object* v_cls_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_getInheritedTraceOptions_1767_ = lean_ctor_get(v_inst_1753_, 2);
lean_inc(v_getInheritedTraceOptions_1767_);
v___x_1768_ = lean_box(v___x_1764_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1769_, 0, v___x_1761_);
lean_closure_set(v___f_1769_, 1, v___x_1768_);
lean_inc_ref(v___f_1769_);
lean_inc(v_modifyEnv_1754_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1770_, 0, v_modifyEnv_1754_);
lean_closure_set(v___f_1770_, 1, v___f_1769_);
v_cls_1771_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__6___closed__1));
lean_inc_n(v_toBind_1756_, 3);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1772_, 0, v_inst_1755_);
lean_closure_set(v___f_1772_, 1, v_toPure_1752_);
lean_closure_set(v___f_1772_, 2, v_cls_1771_);
lean_closure_set(v___f_1772_, 3, v_toBind_1756_);
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1773_, 0, v_modifyEnv_1754_);
lean_closure_set(v___f_1773_, 1, v___f_1769_);
lean_closure_set(v___f_1773_, 2, v_inst_1757_);
lean_closure_set(v___f_1773_, 3, v_inst_1753_);
lean_closure_set(v___f_1773_, 4, v_inst_1758_);
lean_closure_set(v___f_1773_, 5, v_inst_1759_);
lean_closure_set(v___f_1773_, 6, v_cls_1771_);
lean_closure_set(v___f_1773_, 7, v_toBind_1756_);
lean_closure_set(v___f_1773_, 8, v___f_1770_);
v___x_1774_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1767_, v___f_1772_);
v___x_1775_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v___x_1774_, v___f_1773_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_){
_start:
{
lean_object* v_toApplicative_1782_; lean_object* v_toBind_1783_; lean_object* v_getEnv_1784_; lean_object* v_modifyEnv_1785_; lean_object* v_toPure_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; 
v_toApplicative_1782_ = lean_ctor_get(v_inst_1776_, 0);
v_toBind_1783_ = lean_ctor_get(v_inst_1776_, 1);
lean_inc_n(v_toBind_1783_, 2);
v_getEnv_1784_ = lean_ctor_get(v_inst_1777_, 0);
lean_inc(v_getEnv_1784_);
v_modifyEnv_1785_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc(v_modifyEnv_1785_);
lean_dec_ref(v_inst_1777_);
v_toPure_1786_ = lean_ctor_get(v_toApplicative_1782_, 1);
lean_inc(v_toPure_1786_);
v___x_1787_ = lean_box(0);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2), 10, 9);
lean_closure_set(v___f_1788_, 0, v___x_1787_);
lean_closure_set(v___f_1788_, 1, v_toPure_1786_);
lean_closure_set(v___f_1788_, 2, v_inst_1778_);
lean_closure_set(v___f_1788_, 3, v_modifyEnv_1785_);
lean_closure_set(v___f_1788_, 4, v_inst_1779_);
lean_closure_set(v___f_1788_, 5, v_toBind_1783_);
lean_closure_set(v___f_1788_, 6, v_inst_1776_);
lean_closure_set(v___f_1788_, 7, v_inst_1780_);
lean_closure_set(v___f_1788_, 8, v_inst_1781_);
v___x_1789_ = lean_apply_4(v_toBind_1783_, lean_box(0), lean_box(0), v_getEnv_1784_, v___f_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1791_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_unsigned_to_nat(4259277863u);
v___x_1813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1814_ = l_Lean_Name_num___override(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1817_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1818_ = l_Lean_Name_str___override(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1821_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1822_ = l_Lean_Name_str___override(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_unsigned_to_nat(2u);
v___x_1824_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1825_ = l_Lean_Name_num___override(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1827_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__6___closed__1));
v___x_1828_ = 0;
v___x_1829_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1830_ = l_Lean_registerTraceClass(v___x_1827_, v___x_1828_, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1831_;
v_res_1831_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1831_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1833_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_indirectModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_indirectModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_extraModUses = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_extraModUses);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ExtraModUses(builtin);
}
#ifdef __cplusplus
}
#endif
