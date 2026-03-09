// Lean compiler output
// Module: Lake.Config.Dependency
// Imports: public import Init.Dynamic public import Init.System.FilePath public import Lean.Data.NameMap.Basic import Init.Data.ToString.Name import Init.Data.ToString.Macro
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
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_instInhabitedFilePath_default;
static lean_once_cell_t l_Lake_instInhabitedDependencySrc_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedDependencySrc_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedDependencySrc_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedDependencySrc;
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value;
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprDependencySrc_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lake.DependencySrc.path"};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__0 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__1 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__2 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__2_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lake_instReprDependencySrc_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDependencySrc_repr___closed__3;
static lean_once_cell_t l_Lake_instReprDependencySrc_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDependencySrc_repr___closed__4;
static const lean_string_object l_Lake_instReprDependencySrc_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.DependencySrc.git"};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__5 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__5_value)}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__6 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__7 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__7_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprDependencySrc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprDependencySrc_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprDependencySrc___closed__0 = (const lean_object*)&l_Lake_instReprDependencySrc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprDependencySrc = (const lean_object*)&l_Lake_instReprDependencySrc___closed__0_value;
static const lean_string_object l_Lake_instInhabitedDependency_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedDependency_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedDependency_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedDependency_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedDependency_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependency_default = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependency = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__1_value;
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dependency"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value),LEAN_SCALAR_PTR_LITERAL(248, 114, 43, 207, 103, 109, 40, 59)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameDependency = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34__value;
static const lean_string_object l_Lake_Dependency_fullName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_Dependency_fullName___closed__0 = (const lean_object*)&l_Lake_Dependency_fullName___closed__0_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_DependencySrc_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DependencySrc_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DependencySrc_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_DependencySrc_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_DependencySrc_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_DependencySrc_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_DependencySrc_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedDependencySrc_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_instInhabitedFilePath_default;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedDependencySrc_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_instInhabitedDependencySrc_default___closed__0, &l_Lake_instInhabitedDependencySrc_default___closed__0_once, _init_l_Lake_instInhabitedDependencySrc_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedDependencySrc(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedDependencySrc_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
x_5 = x_1;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
x_8 = l_String_quote(x_4);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_9 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Repr_addAppParen(x_10, x_2);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_5 = x_1;
x_6 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
x_8 = lean_unsigned_to_nat(1024u);
x_9 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
x_10 = l_String_quote(x_4);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 0, x_10);
x_11 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Repr_addAppParen(x_12, x_8);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDependencySrc_repr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDependencySrc_repr___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
x_4 = x_1;
x_5 = x_27;
goto block_26;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_6; lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(1024u);
x_23 = lean_nat_dec_le(x_22, x_2);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_obj_once(&l_Lake_instReprDependencySrc_repr___closed__3, &l_Lake_instReprDependencySrc_repr___closed__3_once, _init_l_Lake_instReprDependencySrc_repr___closed__3);
x_6 = x_24;
goto block_21;
}
else
{
lean_object* x_25; 
x_25 = lean_obj_once(&l_Lake_instReprDependencySrc_repr___closed__4, &l_Lake_instReprDependencySrc_repr___closed__4_once, _init_l_Lake_instReprDependencySrc_repr___closed__4);
x_6 = x_25;
goto block_21;
}
block_21:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__2));
x_8 = lean_unsigned_to_nat(1024u);
x_9 = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
x_10 = l_String_quote(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 3);
lean_ctor_set(x_4, 0, x_10);
x_11 = x_4;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_10);
x_11 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Repr_addAppParen(x_12, x_8);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = 0;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_49; uint8_t x_50; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_dec_ref(x_1);
x_49 = lean_unsigned_to_nat(1024u);
x_50 = lean_nat_dec_le(x_49, x_2);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_obj_once(&l_Lake_instReprDependencySrc_repr___closed__3, &l_Lake_instReprDependencySrc_repr___closed__3_once, _init_l_Lake_instReprDependencySrc_repr___closed__3);
x_31 = x_51;
goto block_48;
}
else
{
lean_object* x_52; 
x_52 = lean_obj_once(&l_Lake_instReprDependencySrc_repr___closed__4, &l_Lake_instReprDependencySrc_repr___closed__4_once, _init_l_Lake_instReprDependencySrc_repr___closed__4);
x_31 = x_52;
goto block_48;
}
block_48:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_box(1);
x_33 = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__7));
x_34 = l_String_quote(x_28);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_unsigned_to_nat(1024u);
x_39 = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(x_29, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
x_42 = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(x_30, x_38);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
x_45 = 0;
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = l_Repr_addAppParen(x_46, x_2);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprDependencySrc_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
x_5 = lean_string_append(x_3, x_4);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_2, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
return x_8;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedDependencySrc_default = _init_l_Lake_instInhabitedDependencySrc_default();
lean_mark_persistent(l_Lake_instInhabitedDependencySrc_default);
l_Lake_instInhabitedDependencySrc = _init_l_Lake_instInhabitedDependencySrc();
lean_mark_persistent(l_Lake_instInhabitedDependencySrc);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dependency(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Dependency(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Dependency(builtin);
}
#ifdef __cplusplus
}
#endif
