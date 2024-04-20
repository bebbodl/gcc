
#define __MAKE_MSYS2__

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tree.h"
#include "stringpool.h"
#include "diagnostic-core.h"
#include "attribs.h"
#include "stor-layout.h"
#include "langhooks.h"
#include "plugin.h"

struct lang_hooks lang_hooks;

struct ggc_root_tab;
ggc_root_tab ** gt_pch_scalar_rtab;
ggc_root_tab ** gt_ggc_rtab;
ggc_root_tab ** gt_ggc_deletable_rtab;

static void (* __apply_tm_attr) (tree, tree);
void apply_tm_attr (tree a, tree b)
{
  __apply_tm_attr(a, b);
}

static tree (* __decl_attributes) (tree *, tree, int);
tree decl_attributes (tree *a, tree b, int c)
{
  return __decl_attributes(a, b, c);
}

static tree (* __make_attribute) (const char *, const char *, tree);
tree make_attribute (const char *a, const char *b, tree c) {
  return __make_attribute(a, b, c);
}

static const struct attribute_spec * (*__lookup_attribute_spec) (const_tree);
const struct attribute_spec *lookup_attribute_spec (const_tree a)
{
  return __lookup_attribute_spec(a);
}

static tree (*__get_attribute_name) (const_tree);
tree get_attribute_name (const_tree a)
{
  return __get_attribute_name(a);
}

static tree (*__convert) (tree, tree);
tree convert (tree a, tree b)
{
  return __convert(a, b);
}

static void (*__gt_pch_nx_language_function) (void *);
void
gt_pch_nx_language_function (void *x_p)
{
  __gt_pch_nx_language_function(x_p);
}

static void (* __gt_ggc_mx_language_function) (void *);
void
gt_ggc_mx_language_function (void *x_p)
{
  __gt_ggc_mx_language_function(x_p);
}

static void (*__gt_ggc_mx_lang_tree_node) (void *);
void
gt_ggc_mx_lang_tree_node (void *x_p)
{
  __gt_ggc_mx_lang_tree_node(x_p);
}

static void (*__gt_pch_nx_lang_tree_node) (void *);
void
gt_pch_nx_lang_tree_node (void *x_p)
{
  __gt_pch_nx_lang_tree_node(x_p);
}


static void (*__gt_clear_caches) ();
void
gt_clear_caches ()
{
  __gt_clear_caches();
}


void __set__pointers(struct lang_hooks *p__lang_hooks,
		    ggc_root_tab ** p__gt_pch_scalar_rtab,
		    ggc_root_tab ** p__gt_ggc_rtab,
		    ggc_root_tab ** p__gt_ggc_deletable_rtab,
		     void (*p__apply_tm_attr) (tree, tree),
		     tree (*p__decl_attributes) (tree *, tree, int),
		     tree (*p__make_attribute) (const char *, const char *, tree),
		     const struct attribute_spec * (*p__lookup_attribute_spec) (const_tree),
		     tree (*p__get_attribute_name) (const_tree),
		     tree (*p__convert) (tree, tree),
		     void (*p__gt_pch_nx_language_function) (void *),
		     void (*p__gt_ggc_mx_language_function) (void *),
		     void (*p__gt_ggc_mx_lang_tree_node) (void *),
		     void (*p__gt_pch_nx_lang_tree_node) (void *),
		     void (*p__gt_clear_caches) ()
) {
  memcpy(&lang_hooks, p__lang_hooks, sizeof(struct lang_hooks));

  gt_pch_scalar_rtab = p__gt_pch_scalar_rtab;
  gt_ggc_rtab = p__gt_ggc_rtab;
  gt_ggc_deletable_rtab = p__gt_ggc_deletable_rtab;

  __apply_tm_attr = p__apply_tm_attr;
  __decl_attributes = p__decl_attributes;
  __make_attribute = p__make_attribute;
  __lookup_attribute_spec = p__lookup_attribute_spec;
  __get_attribute_name = p__get_attribute_name;
  __convert = p__convert;
  __gt_pch_nx_language_function = p__gt_pch_nx_language_function;
  __gt_ggc_mx_language_function = p__gt_ggc_mx_language_function;
  __gt_ggc_mx_lang_tree_node = p__gt_ggc_mx_lang_tree_node;
  __gt_pch_nx_lang_tree_node = p__gt_pch_nx_lang_tree_node;
  __gt_clear_caches = p__gt_clear_caches;
}
