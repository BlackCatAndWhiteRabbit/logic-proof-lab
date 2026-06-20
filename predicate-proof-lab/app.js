"use strict";

const STORAGE_KEY = "buaa-predicate-proof-theorems-v1";
const WORKSPACE_STORAGE_KEY = "buaa-predicate-proof-workspace-v1";

const axiomSchemas = [
  {
    id: "A1",
    label: "公理 1",
    text: "A -> (B -> A)",
    ast: null,
  },
  {
    id: "A2",
    label: "公理 2",
    text: "(A -> (B -> C)) -> ((A -> B) -> (A -> C))",
    ast: null,
  },
  {
    id: "A3",
    label: "公理 3",
    text: "(~B -> ~A) -> (A -> B)",
    ast: null,
  },
];

const state = {
  target: null,
  currentGoal: null,
  deductionStack: [],
  steps: [],
  theorems: [],
  acceptedShown: false,
};

const el = {
  targetInput: document.querySelector("#targetInput"),
  setTargetBtn: document.querySelector("#setTargetBtn"),
  targetStatus: document.querySelector("#targetStatus"),
  targetPreview: document.querySelector("#targetPreview"),
  deductionStack: document.querySelector("#deductionStack"),
  enterDeductionBtn: document.querySelector("#enterDeductionBtn"),
  exitDeductionBtn: document.querySelector("#exitDeductionBtn"),
  formulaInputLabel: document.querySelector("#formulaInputLabel"),
  formulaInput: document.querySelector("#formulaInput"),
  sourceModes: document.querySelectorAll("input[name='sourceMode']"),
  premiseControls: document.querySelector("#premiseControls"),
  premiseSelect: document.querySelector("#premiseSelect"),
  mpControls: document.querySelector("#mpControls"),
  mpPremiseInput: document.querySelector("#mpPremiseInput"),
  mpImplicationInput: document.querySelector("#mpImplicationInput"),
  ugControls: document.querySelector("#ugControls"),
  ugStepInput: document.querySelector("#ugStepInput"),
  ugVariableInput: document.querySelector("#ugVariableInput"),
  theoremControls: document.querySelector("#theoremControls"),
  theoremSelect: document.querySelector("#theoremSelect"),
  theoremPremiseControls: document.querySelector("#theoremPremiseControls"),
  addStepBtn: document.querySelector("#addStepBtn"),
  checkCurrentBtn: document.querySelector("#checkCurrentBtn"),
  composerMessage: document.querySelector("#composerMessage"),
  proofBody: document.querySelector("#proofBody"),
  emptyProofTemplate: document.querySelector("#emptyProofTemplate"),
  proofGraph: document.querySelector("#proofGraph"),
  saveTheoremBtn: document.querySelector("#saveTheoremBtn"),
  loadDemoBtn: document.querySelector("#loadDemoBtn"),
  resetProofBtn: document.querySelector("#resetProofBtn"),
  theoremLibrary: document.querySelector("#theoremLibrary"),
  dependencyGraphBtn: document.querySelector("#dependencyGraphBtn"),
  dependencyGraphSection: document.querySelector("#dependencyGraphSection"),
  theoremDependencyGraph: document.querySelector("#theoremDependencyGraph"),
  clearLibraryBtn: document.querySelector("#clearLibraryBtn"),
  acceptedToast: document.querySelector("#acceptedToast"),
};

class Tokenizer {
  constructor(input) {
    this.input = input;
    this.index = 0;
    this.tokens = [];
  }

  scan() {
    while (this.index < this.input.length) {
      const char = this.input[this.index];
      if (/\s/.test(char)) {
        this.index += 1;
        continue;
      }
      if ("()~&|,@?.".includes(char)) {
        this.tokens.push({ type: char, value: char });
        this.index += 1;
        continue;
      }
      if (char === "-" && this.input[this.index + 1] === ">") {
        this.tokens.push({ type: "->", value: "->" });
        this.index += 2;
        continue;
      }
      if (/[A-Za-z]/.test(char)) {
        let value = char;
        this.index += 1;
        while (this.index < this.input.length && /[A-Za-z0-9_]/.test(this.input[this.index])) {
          value += this.input[this.index];
          this.index += 1;
        }
        this.tokens.push({ type: "id", value });
        continue;
      }
      throw new Error(`无法识别的字符 "${char}"`);
    }
    this.tokens.push({ type: "eof", value: "" });
    return this.tokens;
  }
}

class Parser {
  constructor(input) {
    this.tokens = new Tokenizer(input).scan();
    this.index = 0;
  }

  parse() {
    const expression = this.parseImplication();
    if (!this.match("eof")) {
      throw new Error(`公式在 "${this.current().value}" 附近没有解析完`);
    }
    return expression;
  }

  parseImplication() {
    const left = this.parseOr();
    if (this.match("->")) {
      const right = this.parseImplication();
      return { type: "implies", left, right };
    }
    return left;
  }

  parseOr() {
    let node = this.parseAnd();
    while (this.match("|")) {
      node = { type: "or", left: node, right: this.parseAnd() };
    }
    return node;
  }

  parseAnd() {
    let node = this.parsePrefix();
    while (this.match("&")) {
      node = { type: "and", left: node, right: this.parsePrefix() };
    }
    return node;
  }

  parsePrefix() {
    if (this.match("~")) {
      return { type: "not", value: this.parsePrefix() };
    }
    if (this.match("@")) {
      const variable = this.consumeIdentifier("全称量词后需要变量名");
      this.match(".");
      return { type: "forall", variable, body: this.parsePrefix() };
    }
    if (this.match("?")) {
      const variable = this.consumeIdentifier("存在量词后需要变量名");
      this.match(".");
      return { type: "exists", variable, body: this.parsePrefix() };
    }
    return this.parsePrimary();
  }

  parsePrimary() {
    if (this.match("(")) {
      const expression = this.parseImplication();
      this.consume(")", "缺少右括号");
      return expression;
    }

    const name = this.consumeIdentifier("需要谓词名、公式变量或左括号");
    const args = [];
    if (this.match("(")) {
      if (this.match(")")) {
        throw new Error("谓词参数列表不能为空");
      }
      do {
        args.push(this.consumeIdentifier("谓词参数必须是个体变元或常元"));
      } while (this.match(","));
      this.consume(")", "谓词参数列表缺少右括号");
    }
    return { type: "pred", name, args };
  }

  current() {
    return this.tokens[this.index];
  }

  match(type) {
    if (this.current().type !== type) {
      return false;
    }
    this.index += 1;
    return true;
  }

  consume(type, message) {
    if (!this.match(type)) {
      throw new Error(message);
    }
  }

  consumeIdentifier(message) {
    const token = this.current();
    if (!this.match("id")) {
      throw new Error(message);
    }
    return token.value;
  }
}

function normalizeFormulaInput(text) {
  return String(text || "")
    .trim()
    .replace(/^`+|`+$/g, "")
    .replace(/^\$\$([\s\S]*)\$\$/g, "$1")
    .replace(/^\$([\s\S]*)\$/g, "$1")
    .replace(/^\\\(([\s\S]*)\\\)$/g, "$1")
    .replace(/^\\\[([\s\S]*)\\\]$/g, "$1")
    .replace(/\\left\s*/g, "")
    .replace(/\\right\s*/g, "")
    .replace(/\\bigl\s*/g, "")
    .replace(/\\bigr\s*/g, "")
    .replace(/\\Bigl\s*/g, "")
    .replace(/\\Bigr\s*/g, "")
    .replace(/\\forall\b/g, "@")
    .replace(/\\exists\b/g, "?")
    .replace(/\\rightarrow\b/g, "->")
    .replace(/\\Rightarrow\b/g, "->")
    .replace(/\\implies\b/g, "->")
    .replace(/\\to\b/g, "->")
    .replace(/\\vdash\b/g, "⊢")
    .replace(/\\turnstile\b/g, "⊢")
    .replace(/\\neg\b/g, "~")
    .replace(/\\lnot\b/g, "~")
    .replace(/\\sim\b/g, "~")
    .replace(/\\land\b/g, "&")
    .replace(/\\wedge\b/g, "&")
    .replace(/\\lor\b/g, "|")
    .replace(/\\vee\b/g, "|")
    .replace(/\\,/g, " ")
    .replace(/\\;/g, " ")
    .replace(/\\:/g, " ")
    .replace(/\\!/g, "")
    .replace(/\$/g, "")
    .replace(/([@?])\s*\{\s*([A-Za-z][A-Za-z0-9_]*)\s*\}/g, "$1$2")
    .replaceAll("（", "(")
    .replaceAll("）", ")")
    .replaceAll("{", "(")
    .replaceAll("}", ")")
    .replaceAll("，", ",")
    .replaceAll("。", "")
    .replaceAll("；", "")
    .replaceAll("→", "->")
    .replaceAll("⇒", "->")
    .replaceAll("|-", "⊢")
    .replaceAll("¬", "~")
    .replaceAll("～", "~")
    .replaceAll("∧", "&")
    .replaceAll("∨", "|")
    .replaceAll("∀", "@")
    .replaceAll("∃", "?")
    .replace(/\bforall\b/gi, "@")
    .replace(/\ball\b/gi, "@")
    .replace(/\bexists\b/gi, "?")
    .replace(/\bexist\b/gi, "?")
    .replace(/[\s,，。；;]+$/g, "")
    .trim();
}

function parseFormula(text) {
  const trimmed = normalizeFormulaInput(text);
  if (!trimmed) {
    throw new Error("请输入公式");
  }
  assertUnambiguousImplications(trimmed);
  return expandConnectives(new Parser(trimmed).parse());
}

function parseFormulaRaw(text) {
  const trimmed = normalizeFormulaInput(text);
  if (!trimmed) {
    throw new Error("请输入公式");
  }
  assertUnambiguousImplications(trimmed);
  return new Parser(trimmed).parse();
}

function assertUnambiguousImplications(text) {
  const normalized = String(text || "").trim();
  validateImplicationSegment(normalized);
}

function validateImplicationSegment(text) {
  const arrowPositions = [];
  let depth = 0;
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (char === "(") {
      depth += 1;
      continue;
    }
    if (char === ")") {
      depth -= 1;
      continue;
    }
    if (depth === 0 && text.startsWith("->", index)) {
      arrowPositions.push(index);
      index += 1;
    }
  }

  if (arrowPositions.length > 1) {
    throw new Error(`连续使用 -> 时请加括号，例如 A -> (~A -> ~A) 或 (A -> ~A) -> ~A`);
  }

  for (const inner of collectParenthesizedSegments(text)) {
    validateImplicationSegment(inner);
  }
}

function collectParenthesizedSegments(text) {
  const segments = [];
  const stack = [];
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (char === "(") {
      stack.push(index);
    } else if (char === ")" && stack.length) {
      const start = stack.pop();
      segments.push(text.slice(start + 1, index));
    }
  }
  return segments;
}

function expandConnectives(node) {
  if (node.type === "pred") {
    return cloneAst(node);
  }
  if (node.type === "not") {
    return { type: "not", value: expandConnectives(node.value) };
  }
  if (node.type === "forall") {
    return { type: "forall", variable: node.variable, body: expandConnectives(node.body) };
  }
  if (node.type === "exists") {
    return {
      type: "not",
      value: {
        type: "forall",
        variable: node.variable,
        body: { type: "not", value: expandConnectives(node.body) },
      },
    };
  }
  if (node.type === "implies") {
    return { type: "implies", left: expandConnectives(node.left), right: expandConnectives(node.right) };
  }
  if (node.type === "or") {
    return { type: "implies", left: { type: "not", value: expandConnectives(node.left) }, right: expandConnectives(node.right) };
  }
  if (node.type === "and") {
    return {
      type: "not",
      value: {
        type: "implies",
        left: expandConnectives(node.left),
        right: { type: "not", value: expandConnectives(node.right) },
      },
    };
  }
  return cloneAst(node);
}

function normalizeFormulaForDisplay(text) {
  const raw = parseFormulaRaw(text);
  const expanded = expandConnectives(raw);
  return {
    raw,
    expanded,
    rawFormula: formatFormula(raw),
    expandedFormula: formatFormula(expanded),
    changed: !astEquals(raw, expanded),
  };
}

function splitTopLevel(text, separator) {
  const parts = [];
  let depth = 0;
  let start = 0;
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (char === "(") depth += 1;
    if (char === ")") depth -= 1;
    if (char === separator && depth === 0) {
      parts.push(text.slice(start, index).trim());
      start = index + 1;
    }
  }
  parts.push(text.slice(start).trim());
  return parts.filter(Boolean);
}

function findTopLevelTargetSeparator(text) {
  let depth = 0;
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (char === "(") depth += 1;
    if (char === ")") depth -= 1;
    if (depth === 0 && text.startsWith("=>", index)) {
      return { index, length: 2 };
    }
    if (depth === 0 && char === "⊢") {
      return { index, length: 1 };
    }
  }
  return null;
}

function parseTarget(text) {
  const normalized = normalizeFormulaInput(text);
  const separator = findTopLevelTargetSeparator(normalized);
  if (!separator) {
    const ast = parseFormula(normalized);
    const formula = formatFormula(ast);
    return {
      ast,
      assumptions: [],
      premises: [],
      formula,
      conclusionAst: cloneAst(ast),
      conclusionFormula: formula,
      sequentMode: false,
    };
  }

  const premiseText = normalized.slice(0, separator.index).trim();
  const conclusionText = normalized.slice(separator.index + separator.length).trim();
  if (!conclusionText) {
    throw new Error("前提集合后需要写出结论");
  }
  const premises = splitTopLevel(premiseText, ",").map((part) => {
    const ast = parseFormula(part);
    return { ast, formula: formatFormula(ast) };
  });
  const ast = parseFormula(conclusionText);
  const conclusionFormula = formatFormula(ast);
  const formula = premises.length ? `${premises.map((item) => item.formula).join(", ")} => ${conclusionFormula}` : conclusionFormula;
  return {
    ast,
    assumptions: premises,
    premises,
    formula,
    conclusionAst: cloneAst(ast),
    conclusionFormula,
    sequentMode: true,
  };
}

function normalizeTargetForDisplay(text) {
  const normalized = normalizeFormulaInput(text);
  const separator = findTopLevelTargetSeparator(normalized);
  if (!separator) {
    return normalizeFormulaForDisplay(normalized);
  }
  const premiseText = normalized.slice(0, separator.index).trim();
  const conclusionText = normalized.slice(separator.index + separator.length).trim();
  const rawPremises = splitTopLevel(premiseText, ",").map((part) => parseFormulaRaw(part));
  const expandedPremises = rawPremises.map(expandConnectives);
  const rawConclusion = parseFormulaRaw(conclusionText);
  const expandedConclusion = expandConnectives(rawConclusion);
  const rawConclusionFormula = formatFormula(rawConclusion);
  const expandedConclusionFormula = formatFormula(expandedConclusion);
  const rawFormula = rawPremises.length ? `${rawPremises.map(formatFormula).join(", ")} => ${rawConclusionFormula}` : rawConclusionFormula;
  const expandedFormula = expandedPremises.length ? `${expandedPremises.map(formatFormula).join(", ")} => ${expandedConclusionFormula}` : expandedConclusionFormula;
  return { rawFormula, expandedFormula, changed: rawFormula !== expandedFormula };
}

function precedence(node) {
  if (node.type === "implies") return 1;
  if (node.type === "or") return 2;
  if (node.type === "and") return 3;
  if (node.type === "forall" || node.type === "exists") return 4;
  if (node.type === "not") return 5;
  return 6;
}

function formatFormula(node, parentPrecedence = 0, side = "") {
  let text = "";
  if (node.type === "pred") {
    text = node.args.length ? `${node.name}(${node.args.join(",")})` : node.name;
  } else if (node.type === "not") {
    const inner = formatFormula(node.value, precedence(node), "right");
    text = `~${inner}`;
  } else if (node.type === "forall" || node.type === "exists") {
    const symbol = node.type === "forall" ? "@" : "?";
    const body = formatFormula(node.body, precedence(node), "right");
    text = `${symbol}${node.variable} ${body}`;
  } else {
    const op = node.type === "implies" ? "->" : node.type === "and" ? "&" : "|";
    const own = precedence(node);
    const left = formatFormula(node.left, own, "left");
    const right = formatFormula(node.right, own, "right");
    text = `${left} ${op} ${right}`;
  }
  const needsPrecedenceParens = precedence(node) < parentPrecedence;
  const needsImplicationParens = node.type === "implies" && parentPrecedence === precedence(node);
  return needsPrecedenceParens || needsImplicationParens ? `(${text})` : text;
}

function astEquals(a, b) {
  if (!a || !b || a.type !== b.type) return false;
  if (a.type === "pred") {
    return a.name === b.name && a.args.length === b.args.length && a.args.every((arg, index) => arg === b.args[index]);
  }
  if (a.type === "not") return astEquals(a.value, b.value);
  if (a.type === "forall" || a.type === "exists") {
    return a.variable === b.variable && astEquals(a.body, b.body);
  }
  return astEquals(a.left, b.left) && astEquals(a.right, b.right);
}

function cloneAst(node) {
  return JSON.parse(JSON.stringify(node));
}

function makeProofLine(ast, mode, detail, refs = []) {
  return {
    ast: cloneAst(ast),
    formula: formatFormula(ast),
    mode,
    detail,
    refs,
  };
}

function impliesAst(left, right) {
  return {
    type: "implies",
    left: cloneAst(left),
    right: cloneAst(right),
  };
}

function forallAst(variable, body) {
  return {
    type: "forall",
    variable,
    body: cloneAst(body),
  };
}

function isFormulaMeta(node) {
  return node.type === "pred" && node.args.length === 0 && /^[A-Z]$/.test(node.name);
}

function isPredicateMetaName(name) {
  return /^[A-Z][A-Za-z0-9_]*$/.test(name);
}

function createSchemaBindings() {
  return {
    formulas: new Map(),
    predicates: new Map(),
    terms: new Map(),
  };
}

function matchSchema(pattern, actual, bindings = createSchemaBindings()) {
  if (isFormulaMeta(pattern)) {
    const existing = bindings.formulas.get(pattern.name);
    if (!existing) {
      bindings.formulas.set(pattern.name, cloneAst(actual));
      return true;
    }
    return astEquals(existing, actual);
  }

  if (!pattern || !actual || pattern.type !== actual.type) return false;

  if (pattern.type === "pred") {
    if (pattern.args.length !== actual.args.length) return false;
    if (isPredicateMetaName(pattern.name)) {
      const existing = bindings.predicates.get(pattern.name);
      if (!existing) {
        bindings.predicates.set(pattern.name, { name: actual.name, arity: actual.args.length });
      } else if (existing.name !== actual.name || existing.arity !== actual.args.length) {
        return false;
      }
    } else if (pattern.name !== actual.name) {
      return false;
    }
    return pattern.args.every((arg, index) => matchTermSchema(arg, actual.args[index], bindings));
  }

  if (pattern.type === "not") {
    return matchSchema(pattern.value, actual.value, bindings);
  }

  if (pattern.type === "forall" || pattern.type === "exists") {
    if (!matchTermSchema(pattern.variable, actual.variable, bindings)) return false;
    return matchSchema(pattern.body, actual.body, bindings);
  }

  return matchSchema(pattern.left, actual.left, bindings) && matchSchema(pattern.right, actual.right, bindings);
}

function matchTermSchema(patternTerm, actualTerm, bindings) {
  const existing = bindings.terms.get(patternTerm);
  if (!existing) {
    bindings.terms.set(patternTerm, actualTerm);
    return true;
  }
  return existing === actualTerm;
}

function instantiateSchema(node, bindings) {
  if (isFormulaMeta(node) && bindings.formulas.has(node.name)) {
    return cloneAst(bindings.formulas.get(node.name));
  }
  if (node.type === "pred") {
    const predicate = bindings.predicates.get(node.name);
    return {
      type: "pred",
      name: predicate ? predicate.name : node.name,
      args: node.args.map((arg) => bindings.terms.get(arg) || arg),
    };
  }
  if (node.type === "not") {
    return { type: "not", value: instantiateSchema(node.value, bindings) };
  }
  if (node.type === "forall" || node.type === "exists") {
    return {
      type: node.type,
      variable: bindings.terms.get(node.variable) || node.variable,
      body: instantiateSchema(node.body, bindings),
    };
  }
  return {
    type: node.type,
    left: instantiateSchema(node.left, bindings),
    right: instantiateSchema(node.right, bindings),
  };
}

function describeSchemaBindings(bindings) {
  const parts = [];
  for (const [name, value] of bindings.formulas.entries()) {
    parts.push(`${name}=${formatFormula(value)}`);
  }
  for (const [name, value] of bindings.predicates.entries()) {
    if (name !== value.name) parts.push(`${name}=${value.name}`);
  }
  for (const [name, value] of bindings.terms.entries()) {
    if (name !== value) parts.push(`${name}=${value}`);
  }
  return parts.join(", ");
}

function freeVariables(node, bound = new Set()) {
  if (node.type === "pred") {
    return new Set(node.args.filter((arg) => !bound.has(arg)));
  }
  if (node.type === "not") {
    return freeVariables(node.value, bound);
  }
  if (node.type === "forall" || node.type === "exists") {
    const nextBound = new Set(bound);
    nextBound.add(node.variable);
    return freeVariables(node.body, nextBound);
  }
  return unionSets(freeVariables(node.left, bound), freeVariables(node.right, bound));
}

function unionSets(a, b) {
  const result = new Set(a);
  for (const item of b) result.add(item);
  return result;
}

function hasFreeVariable(node, variable) {
  return freeVariables(node).has(variable);
}

function findAxiomMatch(ast) {
  for (const axiom of axiomSchemas) {
    const bindings = createSchemaBindings();
    if (matchSchema(axiom.ast, ast, bindings)) {
      const substitution = describeSchemaBindings(bindings);
      return {
        ok: true,
        axiom,
        detail: substitution ? `${axiom.label}，代换：${substitution}` : axiom.label,
      };
    }
  }

  const axiom4 = checkAxiom4(ast);
  if (axiom4.ok) return axiom4;

  const axiom5 = checkAxiom5(ast);
  if (axiom5.ok) return axiom5;

  return {
    ok: false,
    detail: "不是五条公理中任意一条的合法实例",
  };
}

function checkAxiom4(ast) {
  if (ast.type !== "implies" || ast.left.type !== "forall") {
    return { ok: false };
  }
  const binding = { term: null, blocked: false };
  if (!matchSubstitutionInstance(ast.left.body, ast.right, ast.left.variable, binding, new Set())) {
    return { ok: false };
  }
  if (binding.blocked) {
    return { ok: false, detail: `公理 4 的项 ${binding.term} 在代入时会被量词捕获` };
  }
  return {
    ok: true,
    axiom: { id: "A4", label: "公理 4" },
    detail: `公理 4，全称实例化：${ast.left.variable}:=${binding.term || ast.left.variable}`,
  };
}

function matchSubstitutionInstance(template, actual, variable, binding, bound) {
  if (!template || !actual || template.type !== actual.type) return false;

  if (template.type === "pred") {
    if (template.name !== actual.name || template.args.length !== actual.args.length) return false;
    for (let index = 0; index < template.args.length; index += 1) {
      const expected = template.args[index];
      const got = actual.args[index];
      if (expected === variable && !bound.has(variable)) {
        if (bound.has(got)) {
          binding.term = got;
          binding.blocked = true;
          return false;
        }
        if (!binding.term) {
          binding.term = got;
        } else if (binding.term !== got) {
          return false;
        }
      } else if (expected !== got) {
        return false;
      }
    }
    return true;
  }

  if (template.type === "not") {
    return matchSubstitutionInstance(template.value, actual.value, variable, binding, bound);
  }

  if (template.type === "forall" || template.type === "exists") {
    if (template.variable !== actual.variable) return false;
    if (template.variable === variable) {
      return astEquals(template.body, actual.body);
    }
    const nextBound = new Set(bound);
    nextBound.add(template.variable);
    return matchSubstitutionInstance(template.body, actual.body, variable, binding, nextBound);
  }

  return (
    matchSubstitutionInstance(template.left, actual.left, variable, binding, bound) &&
    matchSubstitutionInstance(template.right, actual.right, variable, binding, bound)
  );
}

function checkAxiom5(ast) {
  if (ast.type !== "implies") return { ok: false };
  if (ast.left.type !== "forall") return { ok: false };
  if (ast.left.body.type !== "implies") return { ok: false };
  if (ast.right.type !== "implies") return { ok: false };
  if (ast.right.right.type !== "forall") return { ok: false };

  const variable = ast.left.variable;
  const premise = ast.left.body.left;
  const consequent = ast.left.body.right;
  if (ast.right.right.variable !== variable) return { ok: false };
  if (!astEquals(premise, ast.right.left)) return { ok: false };
  if (!astEquals(consequent, ast.right.right.body)) return { ok: false };
  if (hasFreeVariable(premise, variable)) {
    return {
      ok: false,
      detail: `公理 5 要求 ${variable} 不在左侧公式 ${formatFormula(premise)} 中自由出现`,
    };
  }
  return {
    ok: true,
    axiom: { id: "A5", label: "公理 5" },
    detail: `公理 5，${variable} 不在 ${formatFormula(premise)} 中自由出现`,
  };
}

function stepAt(number) {
  if (!Number.isInteger(number) || number < 1 || number > state.steps.length) {
    return null;
  }
  return state.steps[number - 1];
}

function deriveMp(premiseNumber, implicationNumber) {
  const premise = stepAt(premiseNumber);
  const implication = stepAt(implicationNumber);
  if (!premise || !implication) {
    return { ok: false, detail: "MP 需要填写已经存在的两个步骤号" };
  }

  const direct = deriveMpOrdered(premise, implication, premiseNumber, implicationNumber);
  if (direct.ok) return direct;

  const swapped = deriveMpOrdered(implication, premise, implicationNumber, premiseNumber);
  if (swapped.ok) {
    return {
      ...swapped,
      detail: `已自动识别两个步骤的角色，${swapped.detail}`,
    };
  }

  return direct;
}

function deriveMpOrdered(premise, implication, premiseNumber, implicationNumber) {
  if (implication.ast.type !== "implies") {
    return { ok: false, detail: `步骤 ${implicationNumber} 不是蕴含式 A -> B` };
  }
  if (!astEquals(implication.ast.left, premise.ast)) {
    return {
      ok: false,
      detail: `步骤 ${implicationNumber} 的前件是 ${formatFormula(implication.ast.left)}，与步骤 ${premiseNumber} 不一致`,
    };
  }
  return {
    ok: true,
    ast: cloneAst(implication.ast.right),
    formula: formatFormula(implication.ast.right),
    detail: `由步骤 ${premiseNumber} 和步骤 ${implicationNumber} 使用 MP 得到`,
    refs: [premiseNumber, implicationNumber],
  };
}

function deriveUg(stepNumber, variable) {
  const step = stepAt(stepNumber);
  const cleanVariable = normalizeTermName(variable);
  if (!step) {
    return { ok: false, detail: "UG 需要填写已经存在的来源步骤号" };
  }
  if (!cleanVariable) {
    return { ok: false, detail: "UG 需要填写量词变量，例如 x" };
  }

  const blockingAssumption = getTargetAssumptions().find((assumption) => hasFreeVariable(assumption.ast, cleanVariable));
  if (blockingAssumption) {
    return {
      ok: false,
      detail: `UG 不允许对 ${cleanVariable} 概括，因为它在当前假设 ${blockingAssumption.formula} 中自由出现`,
    };
  }

  const ast = forallAst(cleanVariable, step.ast);
  return {
    ok: true,
    ast,
    formula: formatFormula(ast),
    detail: `由步骤 ${stepNumber} 使用 UG，对 ${cleanVariable} 全称概括`,
    refs: [stepNumber],
  };
}

function normalizeTermName(value) {
  const trimmed = normalizeFormulaInput(value).trim();
  return /^[A-Za-z][A-Za-z0-9_]*$/.test(trimmed) ? trimmed : "";
}

function deriveTheorem(theoremId) {
  const theorem = state.theorems.find((item) => item.id === theoremId);
  if (!theorem) {
    return { ok: false, detail: "请先在定理库中选择一个定理" };
  }

  const premises = theorem.premises || [];
  if (!premises.length) {
    const expansion = normalizeFormulaForDisplay(el.formulaInput.value || theorem.formula);
    return instantiateTheoremConclusion(theorem, expansion.expanded, expansion);
  }

  const inputs = [...el.theoremPremiseControls.querySelectorAll(".theorem-premise-step")];
  if (inputs.length !== premises.length) {
    return { ok: false, detail: "这个定理需要先填写所有前提对应的步骤号" };
  }

  const bindings = createSchemaBindings();
  const refs = [];
  for (let index = 0; index < premises.length; index += 1) {
    const stepNumber = Number.parseInt(inputs[index].value, 10);
    const step = stepAt(stepNumber);
    if (!step) {
      return { ok: false, detail: `前提 ${index + 1} 需要填写已经存在的步骤号` };
    }
    if (!matchSchema(premises[index].ast, step.ast, bindings)) {
      return {
        ok: false,
        detail: `步骤 ${stepNumber} 不能匹配前提 ${index + 1}：${premises[index].formula}`,
      };
    }
    refs.push(stepNumber);
  }

  const ast = instantiateSchema(theorem.ast, bindings);
  return {
    ok: true,
    ast,
    formula: formatFormula(ast),
    detail: `由定理 ${theorem.formula} 和步骤 ${refs.join(", ")} 得到`,
    theoremId,
    refs,
  };
}

function instantiateTheoremConclusion(theorem, requestedAst, expansion = null) {
  const bindings = createSchemaBindings();
  if (!matchSchema(theorem.ast, requestedAst, bindings)) {
    return {
      ok: false,
      detail: `所选定理 ${theorem.formula} 不能实例化为 ${formatFormula(requestedAst)}`,
    };
  }
  const substitution = describeSchemaBindings(bindings);
  const expansionText = expansion && expansion.changed ? `；已按定义展开：${expansion.rawFormula} = ${expansion.expandedFormula}` : "";
  return {
    ok: true,
    ast: cloneAst(requestedAst),
    formula: formatFormula(requestedAst),
    detail: substitution ? `调用已证定理：${theorem.formula}，代换：${substitution}${expansionText}` : `调用已证定理：${theorem.formula}${expansionText}`,
    theoremId: theorem.id,
    refs: [],
  };
}

function getSelectedMode() {
  const checked = [...el.sourceModes].find((item) => item.checked);
  return checked ? checked.value : "axiom";
}

function readCurrentCandidate() {
  const mode = getSelectedMode();
  if (mode === "mp") {
    const premise = Number.parseInt(el.mpPremiseInput.value, 10);
    const implication = Number.parseInt(el.mpImplicationInput.value, 10);
    return { mode, ...deriveMp(premise, implication) };
  }
  if (mode === "ug") {
    const stepNumber = Number.parseInt(el.ugStepInput.value, 10);
    return { mode, ...deriveUg(stepNumber, el.ugVariableInput.value) };
  }
  if (mode === "premise") {
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (!premise) {
      return { ok: false, detail: "当前目标没有可用的临时假设" };
    }
    return {
      ok: true,
      ast: cloneAst(premise.ast),
      formula: premise.formula,
      mode,
      detail: `临时假设 ${index + 1}`,
      refs: [],
    };
  }
  if (mode === "theorem") {
    return { mode, ...deriveTheorem(el.theoremSelect.value) };
  }

  const expansion = normalizeFormulaForDisplay(el.formulaInput.value);
  const ast = expansion.expanded;
  const axiomResult = findAxiomMatch(ast);
  return { ast, formula: formatFormula(ast), mode, expansion, ...axiomResult };
}

function addStep() {
  try {
    const result = readCurrentCandidate();
    if (!result.ok) {
      setMessage(result.detail, "bad");
      return;
    }
    state.steps.push({
      id: crypto.randomUUID(),
      ast: result.ast,
      formula: result.formula,
      mode: result.mode,
      detail: result.detail,
      refs: result.refs || [],
      theoremId: result.theoremId || null,
      axiomId: result.axiom ? result.axiom.id : null,
    });
    el.formulaInput.value = "";
    el.mpPremiseInput.value = "";
    el.mpImplicationInput.value = "";
    el.ugStepInput.value = "";
    setMessage(`步骤 ${state.steps.length} 已添加：${result.detail}`, "good");
    render();
    persistWorkspace();
  } catch (error) {
    setMessage(error.message, "bad");
  }
}

function checkCurrentInput() {
  try {
    const result = readCurrentCandidate();
    const mode = getSelectedMode();
    const prefix =
      mode === "mp" || mode === "ug" || mode === "theorem"
        ? `可推出：${result.formula}。`
        : mode === "premise"
          ? `可添加临时假设：${result.formula}。`
          : "合法。";
    const expansion = result.expansion && result.expansion.changed ? ` 已按定义展开：${result.expansion.rawFormula} = ${result.expansion.expandedFormula}。` : "";
    setMessage(result.ok ? `${prefix}${result.detail}${expansion}` : result.detail, result.ok ? "good" : "bad");
  } catch (error) {
    setMessage(error.message, "bad");
  }
}

function setMessage(text, kind = "") {
  el.composerMessage.textContent = text;
  el.composerMessage.className = `message-line ${kind}`.trim();
}

function setTarget() {
  try {
    const expansion = normalizeTargetForDisplay(el.targetInput.value);
    state.target = parseTarget(el.targetInput.value);
    state.target.rawFormula = expansion.rawFormula;
    state.target.expandedFormula = expansion.expandedFormula;
    state.target.expandedFromSugar = expansion.changed;
    state.currentGoal = {
      ast: cloneAst(state.target.ast),
      formula: state.target.conclusionFormula,
    };
    state.deductionStack = state.target.sequentMode
      ? state.target.premises.map((premise) => ({ ast: cloneAst(premise.ast), formula: premise.formula }))
      : [];
    state.steps = [];
    state.acceptedShown = false;
    updateTargetPreview();
    const expansionMessage = state.target.expandedFromSugar ? `；已按定义展开：${state.target.rawFormula} = ${state.target.expandedFormula}` : "";
    setMessage(`目标已设为：${state.target.formula}${expansionMessage}`, "good");
    render();
    persistWorkspace();
  } catch (error) {
    el.targetPreview.textContent = error.message;
    el.targetStatus.textContent = "有错误";
    el.targetStatus.className = "status-pill warning";
  }
}

function enterDeductionLayer() {
  if (!state.currentGoal) {
    setMessage("请先设置目标定理", "bad");
    return;
  }
  if (state.currentGoal.ast.type !== "implies") {
    setMessage("当前子目标不是蕴含式，不能继续进入演绎子证明", "bad");
    return;
  }
  state.deductionStack.push({
    ast: cloneAst(state.currentGoal.ast.left),
    formula: formatFormula(state.currentGoal.ast.left),
  });
  state.currentGoal = {
    ast: cloneAst(state.currentGoal.ast.right),
    formula: formatFormula(state.currentGoal.ast.right),
  };
  clearProofForDeductionChange(`已进入一层演绎，当前子目标：${state.currentGoal.formula}`);
}

function exitDeductionLayer() {
  const fixedCount = getFixedPremiseCount();
  if (state.deductionStack.length <= fixedCount) {
    setMessage("当前没有可撤销的演绎假设", "bad");
    return;
  }
  state.deductionStack.pop();
  state.currentGoal = computeGoalFromStack();
  clearProofForDeductionChange(`已撤销一层演绎，当前子目标：${state.currentGoal.formula}`);
}

function clearProofForDeductionChange(message) {
  state.steps = [];
  state.acceptedShown = false;
  updateTargetPreview();
  setMessage(`${message}。证明步骤已清空。`, "good");
  render();
  persistWorkspace();
}

function computeGoalFromStack() {
  let cursor = state.target ? cloneAst(state.target.ast) : null;
  const fixedCount = getFixedPremiseCount();
  for (let index = fixedCount; index < state.deductionStack.length; index += 1) {
    if (!cursor || cursor.type !== "implies") break;
    cursor = cursor.right;
  }
  return {
    ast: cursor,
    formula: cursor ? formatFormula(cursor) : "",
  };
}

function updateTargetPreview() {
  if (!state.target || !state.currentGoal) {
    el.targetPreview.textContent = "";
    return;
  }
  const assumptions = getTargetAssumptions();
  const prefix = assumptions.length ? `${assumptions.map((item) => item.formula).join(", ")} ⊢ ` : "";
  el.targetPreview.textContent = `原始目标：${state.target.formula}；当前子目标：${prefix}${state.currentGoal.formula}`;
}

function isGoalProved() {
  if (!state.target || !state.currentGoal) return false;
  return state.steps.some((step) => astEquals(step.ast, state.currentGoal.ast));
}

function saveCurrentTheorem() {
  if (!state.target || !isGoalProved()) {
    return;
  }
  const theoremPremises = state.target.sequentMode ? state.target.premises || [] : [];
  const exists = state.theorems.some((item) => astEquals(item.ast, state.target.ast) && premiseListsEqual(item.premises || [], theoremPremises));
  if (exists) {
    setMessage("定理库里已经有这个定理了", "bad");
    return;
  }
  state.theorems.push({
    id: crypto.randomUUID(),
    ast: cloneAst(state.target.ast),
    premises: theoremPremises.map((premise) => ({
      ast: cloneAst(premise.ast),
      formula: premise.formula,
    })),
    formula: state.target.formula,
    conclusionFormula: state.target.conclusionFormula,
    title: state.target.formula,
    proofSteps: snapshotProofSteps(),
    dependencies: collectProofDependencies(state.steps),
    proofLength: state.steps.length,
    createdAt: new Date().toISOString(),
  });
  persistTheorems();
  setMessage(`已保存定理：${state.target.formula}`, "good");
  render();
}

function snapshotProofSteps() {
  return state.steps.map((step, index) => ({
    number: index + 1,
    ast: cloneAst(step.ast),
    formula: step.formula,
    mode: step.mode,
    detail: step.detail,
    refs: [...(step.refs || [])],
    theoremId: step.theoremId || null,
    axiomId: step.axiomId || null,
  }));
}

function collectProofDependencies(steps) {
  return [...new Set(steps.map((step) => step.theoremId).filter(Boolean))];
}

function persistWorkspace() {
  const storage = getWorkspaceStorage();
  if (!storage) return;
  const payload = {
    targetInput: el.targetInput.value,
    target: state.target,
    currentGoal: state.currentGoal,
    deductionStack: state.deductionStack,
    steps: state.steps,
    savedAt: new Date().toISOString(),
  };
  storage.setItem(WORKSPACE_STORAGE_KEY, JSON.stringify(payload));
}

function loadWorkspace() {
  const storage = getWorkspaceStorage();
  if (!storage) return false;
  try {
    const raw = storage.getItem(WORKSPACE_STORAGE_KEY);
    if (!raw) return false;
    const payload = JSON.parse(raw);
    if (!payload || !payload.target || !payload.currentGoal) {
      return false;
    }

    state.target = payload.target;
    state.currentGoal = payload.currentGoal;
    state.deductionStack = Array.isArray(payload.deductionStack) ? payload.deductionStack : [];
    state.steps = Array.isArray(payload.steps) ? payload.steps : [];
    state.acceptedShown = false;
    el.targetInput.value = payload.targetInput || payload.target.formula || "";

    restoreFormulaFields();
    updateTargetPreview();
    return true;
  } catch {
    storage.removeItem(WORKSPACE_STORAGE_KEY);
    return false;
  }
}

function getWorkspaceStorage() {
  try {
    return window.sessionStorage || null;
  } catch {
    return null;
  }
}

function clearLegacySharedWorkspace() {
  try {
    localStorage.removeItem(WORKSPACE_STORAGE_KEY);
  } catch {
    // Ignore storage permission errors.
  }
}

function restoreFormulaFields() {
  if (state.target && state.target.ast) {
    state.target.formula = state.target.formula || formatFormula(state.target.ast);
    state.target.conclusionFormula = state.target.conclusionFormula || formatFormula(state.target.ast);
    state.target.premises = (state.target.premises || []).map((premise) => ({
      ast: premise.ast,
      formula: premise.formula || formatFormula(premise.ast),
    }));
  }
  if (state.currentGoal && state.currentGoal.ast) {
    state.currentGoal.formula = state.currentGoal.formula || formatFormula(state.currentGoal.ast);
  }
  state.deductionStack = (state.deductionStack || []).map((item) => ({
    ast: item.ast,
    formula: item.formula || formatFormula(item.ast),
  }));
  state.steps = (state.steps || []).map((step) => ({
    ...step,
    formula: step.formula || formatFormula(step.ast),
    refs: step.refs || [],
    theoremId: step.theoremId || null,
    axiomId: step.axiomId || null,
  }));
}

function getTheoremExportOrder(rootId) {
  const idToTheorem = new Map(state.theorems.map((theorem) => [theorem.id, theorem]));
  const visited = new Set();
  const visiting = new Set();
  const order = [];

  function visit(id) {
    if (visited.has(id)) return;
    if (visiting.has(id)) return;
    const theorem = idToTheorem.get(id);
    if (!theorem) return;
    visiting.add(id);
    for (const dependencyId of theorem.dependencies || []) {
      visit(dependencyId);
    }
    visiting.delete(id);
    visited.add(id);
    order.push(id);
  }

  visit(rootId);
  return order;
}

function buildTheoremMarkdown(rootId) {
  const idToTheorem = new Map(state.theorems.map((theorem) => [theorem.id, theorem]));
  const root = idToTheorem.get(rootId);
  if (!root) {
    return "";
  }

  const orderedIds = getTheoremExportOrder(rootId);
  const lemmaIds = orderedIds.filter((id) => id !== rootId);
  const lemmaNumbers = new Map(lemmaIds.map((id, index) => [id, index + 1]));
  const sections = [];

  for (const id of orderedIds) {
    const theorem = idToTheorem.get(id);
    if (!theorem) continue;
    const isRoot = id === rootId;
    const title = isRoot ? `定理：${formulaMarkdown(theorem.ast, theorem.formula)}` : `引理${lemmaNumbers.get(id)}：${formulaMarkdown(theorem.ast, theorem.formula)}`;
    const directLemmaRefs = getDirectLemmaReferences(theorem, lemmaNumbers, rootId);
    const deductionExport = getDeductionExport(theorem);
    const lines = [title];
    if (directLemmaRefs.length) {
      lines.push(`本证明引用了：${directLemmaRefs.join("、")}。`);
    }
    if (deductionExport) {
      lines.push(`由演绎定理命题转化为：${deductionExport}`);
    }
    lines.push("证明如下：");
    const proofSteps = theorem.proofSteps || [];
    if (!proofSteps.length) {
      lines.push("（保存时没有证明步骤快照。）");
    } else {
      proofSteps.forEach((step, index) => {
        lines.push(`（${index + 1}）${formulaMarkdown(step.ast, step.formula)}（${getExportStepSource(step, lemmaNumbers, rootId)}）`);
      });
    }
    sections.push(lines.join("\n"));
  }

  return `${sections.join("\n\n")}\n`;
}

function getDirectLemmaReferences(theorem, lemmaNumbers, rootId) {
  return [...new Set((theorem.dependencies || []).filter((id) => id !== rootId && lemmaNumbers.has(id)).map((id) => `引理${lemmaNumbers.get(id)}`))];
}

function getDeductionExport(theorem) {
  const proofSteps = theorem.proofSteps || [];
  const premiseSteps = proofSteps.filter((step) => step.mode === "premise");
  if (!premiseSteps.length || !theorem.ast) {
    return "";
  }

  const converted = collectDeductionPremisesFromImplication(theorem.ast, premiseSteps);
  if (!converted.premises.length) {
    return "";
  }

  const premiseText = converted.premises.map(formatFormulaLatex).join(", ");
  return inlineMath(`${premiseText} \\vdash ${formatFormulaLatex(converted.conclusion)}`);
}

function collectDeductionPremisesFromImplication(ast, premiseSteps) {
  const premises = [];
  let cursor = ast;
  while (cursor && cursor.type === "implies") {
    if (!hasMatchingPremiseStep(cursor.left, premiseSteps)) {
      break;
    }
    premises.push(cloneAst(cursor.left));
    cursor = cursor.right;
  }
  return {
    premises,
    conclusion: cursor || ast,
  };
}

function hasMatchingPremiseStep(ast, premiseSteps) {
  return premiseSteps.some((step) => {
    if (step.ast && astEquals(step.ast, ast)) {
      return true;
    }
    return step.formula && step.formula === formatFormula(ast);
  });
}

function getExportStepSource(step, lemmaNumbers, rootId) {
  if (step.mode === "axiom") {
    return step.axiomId ? `公理${String(step.axiomId).replace(/^A/, "")}` : "公理";
  }
  if (step.mode === "mp") {
    return "MP";
  }
  if (step.mode === "ug") {
    return "UG";
  }
  if (step.mode === "premise") {
    return "临时假设";
  }
  if (step.mode === "theorem") {
    if (step.theoremId && step.theoremId !== rootId && lemmaNumbers.has(step.theoremId)) {
      return `引理${lemmaNumbers.get(step.theoremId)}`;
    }
    return "已证定理";
  }
  return getSourceText(step.mode);
}

function formulaMarkdown(ast, fallbackFormula = "") {
  let formulaAst = ast;
  if (!formulaAst && fallbackFormula) {
    try {
      formulaAst = parseFormula(fallbackFormula);
    } catch {
      formulaAst = null;
    }
  }
  return formulaAst ? inlineMath(formatFormulaLatex(formulaAst)) : inlineMath(escapeLatexText(fallbackFormula || ""));
}

function inlineMath(content) {
  return `$${content}$`;
}

function formatFormulaLatex(node, parentPrecedence = 0, side = "") {
  let text = "";
  if (node.type === "pred") {
    text = node.args.length ? `${latexIdentifier(node.name)}(${node.args.map(latexIdentifier).join(",")})` : latexIdentifier(node.name);
  } else if (node.type === "not") {
    const inner = formatFormulaLatex(node.value, precedence(node), "right");
    text = `\\neg ${inner}`;
  } else if (node.type === "forall" || node.type === "exists") {
    const symbol = node.type === "forall" ? "\\forall" : "\\exists";
    const body = formatFormulaLatex(node.body, precedence(node), "right");
    text = `${symbol} ${latexIdentifier(node.variable)} ${body}`;
  } else {
    const op = node.type === "implies" ? "\\to" : node.type === "and" ? "\\land" : "\\lor";
    const own = precedence(node);
    const left = formatFormulaLatex(node.left, own, "left");
    const right = formatFormulaLatex(node.right, own, "right");
    text = `${left} ${op} ${right}`;
  }
  const needsPrecedenceParens = precedence(node) < parentPrecedence;
  const needsImplicationParens = node.type === "implies" && parentPrecedence === precedence(node);
  return needsPrecedenceParens || needsImplicationParens ? `(${text})` : text;
}

function latexIdentifier(value) {
  return String(value).replace(/_/g, "\\_");
}

function escapeLatexText(value) {
  return String(value)
    .replace(/\\/g, "\\backslash ")
    .replace(/_/g, "\\_")
    .replace(/\$/g, "\\$");
}

async function exportTheoremMarkdown(theoremId) {
  const theorem = state.theorems.find((item) => item.id === theoremId);
  if (!theorem) return;
  const markdown = buildTheoremMarkdown(theoremId);
  if (!markdown) return;

  try {
    await copyTextToClipboard(markdown);
    setMessage(`已复制 Markdown 证明到剪贴板：${theorem.formula}`, "good");
  } catch {
    setMessage("浏览器拒绝写入剪贴板，请在本地服务页面中重试，或检查剪贴板权限。", "bad");
  }
}

async function copyTextToClipboard(text) {
  if (navigator.clipboard && window.isSecureContext) {
    await navigator.clipboard.writeText(text);
    return;
  }

  const textarea = document.createElement("textarea");
  textarea.value = text;
  textarea.setAttribute("readonly", "");
  textarea.style.position = "fixed";
  textarea.style.left = "-9999px";
  textarea.style.top = "0";
  document.body.appendChild(textarea);
  textarea.focus();
  textarea.select();
  const ok = document.execCommand("copy");
  textarea.remove();
  if (!ok) {
    throw new Error("copy failed");
  }
}

function premiseListsEqual(a, b) {
  if (a.length !== b.length) return false;
  return a.every((premise, index) => astEquals(premise.ast, b[index].ast));
}

function getTargetAssumptions() {
  return state.deductionStack || [];
}

function getFixedPremiseCount() {
  return state.target && state.target.sequentMode ? (state.target.premises || []).length : 0;
}

function persistTheorems() {
  const payload = state.theorems.map((item) => ({
    id: item.id,
    ast: item.ast,
    premises: item.premises || [],
    formula: item.formula,
    conclusionFormula: item.conclusionFormula || formatFormula(item.ast),
    title: item.title,
    proofLength: item.proofLength,
    proofSteps: item.proofSteps || [],
    dependencies: item.dependencies || collectProofDependencies(item.proofSteps || []),
    createdAt: item.createdAt,
  }));
  localStorage.setItem(STORAGE_KEY, JSON.stringify(payload));
}

function loadTheorems() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) {
      state.theorems = [];
      return;
    }
    state.theorems = JSON.parse(raw).map((item) => ({
      ...item,
      ast: item.ast,
      premises: (item.premises || []).map((premise) => ({
        ast: premise.ast,
        formula: premise.formula || formatFormula(premise.ast),
      })),
      conclusionFormula: item.conclusionFormula || formatFormula(item.ast),
      proofSteps: item.proofSteps || [],
      dependencies: item.dependencies || collectProofDependencies(item.proofSteps || []),
      formula:
        item.formula ||
        ((item.premises || []).length
          ? `${item.premises.map((premise) => premise.formula || formatFormula(premise.ast)).join(", ")} => ${formatFormula(item.ast)}`
          : formatFormula(item.ast)),
    }));
  } catch {
    state.theorems = [];
  }
}

function clearLibrary() {
  if (!state.theorems.length) return;
  const ok = window.confirm("确定要清空定理库吗？这不会影响当前证明步骤。");
  if (!ok) return;
  state.theorems = [];
  persistTheorems();
  render();
}

function resetProof() {
  state.steps = [];
  state.acceptedShown = false;
  setMessage("证明区已清空", "good");
  render();
  persistWorkspace();
}

function loadDemo() {
  state.steps = [];
  state.deductionStack = [];
  state.acceptedShown = false;
  el.targetInput.value = "@x P(x) -> P(a)";
  setTarget();
  el.formulaInput.value = "@x P(x) -> P(a)";
  selectMode("axiom");
  const result = readCurrentCandidate();
  if (result.ok) {
    state.steps.push({
      id: crypto.randomUUID(),
      ast: result.ast,
      formula: result.formula,
      mode: result.mode,
      detail: result.detail,
      refs: result.refs || [],
      theoremId: null,
      axiomId: result.axiom ? result.axiom.id : null,
    });
  }
  el.formulaInput.value = "";
  setMessage("已载入公理 4 示例证明", "good");
  render();
  persistWorkspace();
}

function selectMode(mode) {
  el.sourceModes.forEach((item) => {
    item.checked = item.value === mode;
  });
  updateModeControls();
}

function updateModeControls() {
  const mode = getSelectedMode();
  el.premiseControls.classList.toggle("is-hidden", mode !== "premise");
  el.mpControls.classList.toggle("is-hidden", mode !== "mp");
  el.ugControls.classList.toggle("is-hidden", mode !== "ug");
  el.theoremControls.classList.toggle("is-hidden", mode !== "theorem");
  const autoMode = mode === "mp" || mode === "premise" || mode === "ug";
  el.formulaInput.disabled = autoMode;
  el.formulaInputLabel.textContent =
    mode === "mp"
      ? "MP 自动推出的公式"
      : mode === "premise"
        ? "选中假设的公式"
        : mode === "ug"
          ? "UG 自动推出的公式"
          : mode === "theorem"
            ? "定理实例化公式"
            : "新步骤公式";
  el.formulaInput.placeholder =
    mode === "mp"
      ? "选择两个步骤后，系统会自动推出结论"
      : mode === "premise"
        ? "选择临时假设后自动填入"
        : mode === "ug"
          ? "填写来源步骤和变量后自动推出"
          : mode === "theorem"
            ? "无前提定理可在这里写目标实例"
            : "例如：@x P(x) -> P(a)";
  el.addStepBtn.textContent = mode === "mp" ? "应用 MP" : mode === "ug" ? "应用 UG" : mode === "theorem" ? "调用定理" : "添加步骤";
  el.checkCurrentBtn.textContent = mode === "mp" ? "预览 MP 结论" : mode === "ug" ? "预览 UG 结论" : mode === "theorem" ? "预览定理结论" : "检查当前输入";
  if (autoMode) {
    el.formulaInput.value = "";
  }
  if (mode === "premise") {
    renderPremiseOptions();
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (premise) el.formulaInput.value = premise.formula;
  }
  if (mode === "theorem") {
    renderTheoremPremiseControls();
    const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value) || state.theorems[0];
    if (theorem) {
      el.formulaInput.disabled = false;
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
    }
  }
}

function renderPremiseOptions() {
  el.premiseSelect.innerHTML = "";
  const premises = getTargetAssumptions();
  if (!premises.length) {
    el.premiseSelect.innerHTML = `<option value="">当前目标没有可拆出的临时假设</option>`;
    return;
  }
  premises.forEach((premise, index) => {
    const option = document.createElement("option");
    option.value = String(index);
    option.textContent = `${index + 1}. ${premise.formula}`;
    el.premiseSelect.appendChild(option);
  });
}

function renderDeductionStack() {
  el.deductionStack.innerHTML = "";
  if (!state.target) {
    el.deductionStack.innerHTML = `<div class="empty-state">先设置一个目标定理。</div>`;
    return;
  }
  if (!state.deductionStack.length) {
    const empty = document.createElement("div");
    empty.className = "stack-item";
    empty.innerHTML = `<span>当前子目标</span><code>${escapeHtml(state.currentGoal.formula)}</code>`;
    el.deductionStack.appendChild(empty);
    return;
  }
  state.deductionStack.forEach((item, index) => {
    const node = document.createElement("div");
    node.className = "stack-item";
    const label = index < getFixedPremiseCount() ? `目标前提 ${index + 1}` : `演绎假设 ${index - getFixedPremiseCount() + 1}`;
    node.innerHTML = `<span>${label}</span><code>${escapeHtml(item.formula)}</code>`;
    el.deductionStack.appendChild(node);
  });
  const goal = document.createElement("div");
  goal.className = "stack-item current-goal";
  goal.innerHTML = `<span>当前子目标</span><code>${escapeHtml(state.currentGoal.formula)}</code>`;
  el.deductionStack.appendChild(goal);
}

function renderTheoremPremiseControls() {
  el.theoremPremiseControls.innerHTML = "";
  const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value);
  if (!theorem || !(theorem.premises || []).length) {
    return;
  }
  theorem.premises.forEach((premise, index) => {
    const label = document.createElement("label");
    label.textContent = `前提 ${index + 1}：${premise.formula}`;
    const input = document.createElement("input");
    input.className = "theorem-premise-step";
    input.type = "number";
    input.min = "1";
    input.placeholder = "对应步骤号";
    label.appendChild(input);
    el.theoremPremiseControls.appendChild(label);
  });
}

function removeStep(index) {
  state.steps.splice(index, 1);
  state.acceptedShown = false;
  state.steps.forEach((step) => {
    step.refs = step.refs.filter((ref) => ref !== index + 1).map((ref) => (ref > index + 1 ? ref - 1 : ref));
    if ((step.mode === "mp" && step.refs.length !== 2) || (step.mode === "ug" && step.refs.length !== 1)) {
      step.detail = "依赖步骤被删除，请重新检查该步骤";
    }
  });
  render();
  persistWorkspace();
}

function renderProofTable() {
  el.proofBody.innerHTML = "";
  if (!state.steps.length) {
    el.proofBody.appendChild(el.emptyProofTemplate.content.cloneNode(true));
    return;
  }
  state.steps.forEach((step, index) => {
    const row = document.createElement("tr");
    row.innerHTML = `
      <td><span class="proof-index">${index + 1}</span></td>
      <td><div class="formula-text">${escapeHtml(step.formula)}</div></td>
      <td><span class="source-badge ${step.mode}">${getSourceText(step.mode)}</span></td>
      <td>${escapeHtml(step.detail)}</td>
      <td><button class="delete-step" title="删除步骤" aria-label="删除步骤 ${index + 1}">×</button></td>
    `;
    row.querySelector("button").addEventListener("click", () => removeStep(index));
    el.proofBody.appendChild(row);
  });
}

function getSourceText(mode) {
  if (mode === "axiom") return "公理";
  if (mode === "premise") return "假设";
  if (mode === "mp") return "MP";
  if (mode === "ug") return "UG";
  if (mode === "theorem") return "定理";
  return "步骤";
}

function renderGraph() {
  el.proofGraph.innerHTML = "";
  const stage = document.createElement("div");
  stage.className = "graph-stage";
  const width = Math.max(720, state.steps.length * 230 + 80);
  const rows = Math.max(1, Math.ceil(state.steps.length / 3));
  const height = Math.max(300, rows * 145 + 40);
  stage.style.width = `${width}px`;
  stage.style.height = `${height}px`;

  const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.classList.add("graph-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.innerHTML = `
    <defs>
      <marker id="arrow" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth">
        <path d="M0,0 L0,6 L9,3 z" fill="#7a8b87"></path>
      </marker>
    </defs>
  `;
  stage.appendChild(svg);

  if (!state.steps.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "添加步骤后，这里会出现证明依赖图。";
    stage.appendChild(empty);
    el.proofGraph.appendChild(stage);
    return;
  }

  const positions = state.steps.map((_, index) => {
    const col = index % 3;
    const row = Math.floor(index / 3);
    return { x: 36 + col * 230 + row * 24, y: 34 + row * 140 };
  });

  state.steps.forEach((step, index) => {
    for (const ref of step.refs) {
      const from = positions[ref - 1];
      const to = positions[index];
      if (!from || !to) continue;
      const line = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const startX = from.x + 190;
      const startY = from.y + 43;
      const endX = to.x;
      const endY = to.y + 43;
      const midX = (startX + endX) / 2;
      line.setAttribute("d", `M ${startX} ${startY} C ${midX} ${startY}, ${midX} ${endY}, ${endX} ${endY}`);
      line.setAttribute("fill", "none");
      line.setAttribute("stroke", "#7a8b87");
      line.setAttribute("stroke-width", "2");
      line.setAttribute("marker-end", "url(#arrow)");
      svg.appendChild(line);
    }
  });

  state.steps.forEach((step, index) => {
    const position = positions[index];
    const goal = state.currentGoal && astEquals(step.ast, state.currentGoal.ast);
    const node = document.createElement("div");
    node.className = `graph-node ${goal ? "is-goal" : ""}`;
    node.style.left = `${position.x}px`;
    node.style.top = `${position.y}px`;
    node.innerHTML = `
      <small>#${index + 1} · ${getSourceText(step.mode)}</small>
      <strong>${escapeHtml(step.formula)}</strong>
      <span>${escapeHtml(step.refs.length ? `依赖 ${step.refs.join(", ")}` : "基础节点")}</span>
    `;
    stage.appendChild(node);
  });

  el.proofGraph.appendChild(stage);
}

function renderLibrary() {
  el.theoremLibrary.innerHTML = "";
  el.theoremSelect.innerHTML = "";
  if (!state.theorems.length) {
    el.theoremLibrary.innerHTML = `<div class="empty-state">证明目标完成后，可以把它保存为后续可调用定理。</div>`;
    el.theoremSelect.innerHTML = `<option value="">暂无可调用定理</option>`;
    return;
  }
  state.theorems.forEach((theorem, index) => {
    const option = document.createElement("option");
    option.value = theorem.id;
    option.textContent = theorem.formula;
    el.theoremSelect.appendChild(option);

    const item = document.createElement("div");
    item.className = "library-item";
    const proofSteps = theorem.proofSteps || [];
    const dependencies = theorem.dependencies || [];
    item.innerHTML = `
      <div class="library-item-head">
        <button type="button" class="library-pick">
          <div class="library-meta"><span>定理 ${index + 1}</span><span>${proofSteps.length || theorem.proofLength || 1} 步证明 · 依赖 ${dependencies.length}</span></div>
          <code>${escapeHtml(theorem.formula)}</code>
        </button>
        <button type="button" class="export-theorem" title="导出 Markdown 证明" aria-label="导出定理 ${index + 1} 的 Markdown 证明">导出</button>
        <button type="button" class="delete-theorem" title="删除定理 ${index + 1}" aria-label="删除定理 ${index + 1}">×</button>
      </div>
      <details class="proof-snapshot">
        <summary>保存的证明步骤</summary>
        <ol>
          ${proofSteps.length ? proofSteps.map((step) => `<li><code>${escapeHtml(step.formula)}</code><span>${escapeHtml(getSourceText(step.mode))} · ${escapeHtml(step.detail || "")}</span></li>`).join("") : "<li>旧版本保存的定理没有步骤快照。</li>"}
        </ol>
      </details>
    `;
    item.querySelector(".library-pick").addEventListener("click", () => {
      el.theoremSelect.value = theorem.id;
      selectMode("theorem");
      el.theoremSelect.value = theorem.id;
      renderTheoremPremiseControls();
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
      setMessage(`已选中定理：${theorem.formula}`, "good");
    });
    item.querySelector(".export-theorem").addEventListener("click", () => exportTheoremMarkdown(theorem.id));
    item.querySelector(".delete-theorem").addEventListener("click", () => deleteTheorem(theorem.id));
    el.theoremLibrary.appendChild(item);
  });
}

function deleteTheorem(theoremId) {
  const theorem = state.theorems.find((item) => item.id === theoremId);
  if (!theorem) return;
  const ok = window.confirm(`确定删除定理：${theorem.formula}？`);
  if (!ok) return;
  state.theorems = state.theorems
    .filter((item) => item.id !== theoremId)
    .map((item) => ({
      ...item,
      dependencies: (item.dependencies || []).filter((id) => id !== theoremId),
      proofSteps: (item.proofSteps || []).map((step) => (step.theoremId === theoremId ? { ...step, theoremId: null, detail: `${step.detail || ""}（引用定理已删除）` } : step)),
    }));
  persistTheorems();
  setMessage(`已删除定理：${theorem.formula}`, "good");
  if (el.dependencyGraphSection && !el.dependencyGraphSection.classList.contains("is-hidden")) {
    el.dependencyGraphSection.classList.add("is-hidden");
    renderTheoremDependencyGraph();
  }
  render();
}

function renderTheoremDependencyGraph() {
  el.dependencyGraphSection.classList.toggle("is-hidden");
  if (el.dependencyGraphSection.classList.contains("is-hidden")) {
    return;
  }
  el.theoremDependencyGraph.innerHTML = "";
  if (!state.theorems.length) {
    el.theoremDependencyGraph.innerHTML = `<div class="empty-state">定理库为空，暂无依赖关系。</div>`;
    return;
  }

  const idToIndex = new Map(state.theorems.map((theorem, index) => [theorem.id, index]));
  const levels = computeTheoremDepthLevels();
  const maxLevel = Math.max(0, ...levels);
  const levelBuckets = Array.from({ length: maxLevel + 1 }, () => []);
  levels.forEach((level, index) => {
    levelBuckets[level].push(index);
  });
  const maxRows = Math.max(1, ...levelBuckets.map((bucket) => bucket.length));
  const width = Math.max(920, (maxLevel + 1) * 330 + 80);
  const height = Math.max(300, maxRows * 170 + 80);
  const stage = document.createElement("div");
  stage.className = "dependency-stage";
  stage.style.width = `${width}px`;
  stage.style.height = `${height}px`;

  const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.classList.add("graph-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  stage.appendChild(svg);

  const positions = state.theorems.map((_, index) => {
    const level = levels[index];
    const row = levelBuckets[level].indexOf(index);
    return { x: 40 + level * 330, y: 40 + row * 170 };
  });

  state.theorems.forEach((theorem, index) => {
    for (const dependencyId of theorem.dependencies || []) {
      const depIndex = idToIndex.get(dependencyId);
      if (depIndex === undefined) continue;
      const from = positions[depIndex];
      const to = positions[index];
      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const startX = from.x + 260;
      const startY = from.y + 43;
      const endX = to.x;
      const endY = to.y + 43;
      const midX = (startX + endX) / 2;
      path.setAttribute("d", `M ${startX} ${startY} C ${midX} ${startY}, ${midX} ${endY}, ${endX} ${endY}`);
      path.setAttribute("fill", "none");
      path.setAttribute("stroke", "#7a8b87");
      path.setAttribute("stroke-width", "2");
      svg.appendChild(path);

      const arrow = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const arrowX = midX;
      const arrowY = (startY + endY) / 2;
      const direction = endX >= startX ? 1 : -1;
      arrow.setAttribute("d", `M ${arrowX + direction * 11} ${arrowY} L ${arrowX - direction * 8} ${arrowY - 8} L ${arrowX - direction * 8} ${arrowY + 8} Z`);
      arrow.setAttribute("fill", "#7a8b87");
      arrow.setAttribute("opacity", "0.92");
      svg.appendChild(arrow);
    }
  });

  state.theorems.forEach((theorem, index) => {
    const node = document.createElement("div");
    node.className = "dependency-node";
    node.style.left = `${positions[index].x}px`;
    node.style.top = `${positions[index].y}px`;
    node.innerHTML = `<small>定理 ${index + 1}</small><code>${escapeHtml(theorem.formula)}</code>`;
    stage.appendChild(node);
  });
  el.theoremDependencyGraph.appendChild(stage);
}

function computeTheoremDepthLevels() {
  const idToIndex = new Map(state.theorems.map((theorem, index) => [theorem.id, index]));
  const memo = new Map();
  const visiting = new Set();

  function depth(index) {
    if (memo.has(index)) return memo.get(index);
    if (visiting.has(index)) return 0;
    visiting.add(index);
    const deps = (state.theorems[index].dependencies || [])
      .map((id) => idToIndex.get(id))
      .filter((item) => item !== undefined);
    const value = deps.length ? Math.max(...deps.map((depIndex) => depth(depIndex))) + 1 : 0;
    visiting.delete(index);
    memo.set(index, value);
    return value;
  }

  return state.theorems.map((_, index) => depth(index));
}

function renderTargetStatus() {
  if (!state.target) {
    el.targetStatus.textContent = "待开始";
    el.targetStatus.className = "status-pill neutral";
    el.saveTheoremBtn.disabled = true;
    el.enterDeductionBtn.disabled = true;
    el.exitDeductionBtn.disabled = true;
    return;
  }
  el.enterDeductionBtn.disabled = !state.currentGoal || state.currentGoal.ast.type !== "implies";
  el.exitDeductionBtn.disabled = state.deductionStack.length <= getFixedPremiseCount();
  if (isGoalProved()) {
    el.targetStatus.textContent = "已证明";
    el.targetStatus.className = "status-pill success";
    el.saveTheoremBtn.disabled = false;
    showAccepted();
  } else {
    el.targetStatus.textContent = "证明中";
    el.targetStatus.className = "status-pill warning";
    el.saveTheoremBtn.disabled = true;
  }
}

function showAccepted() {
  if (state.acceptedShown || !el.acceptedToast) return;
  state.acceptedShown = true;
  el.acceptedToast.classList.remove("show");
  void el.acceptedToast.offsetWidth;
  el.acceptedToast.classList.add("show");
}

function render() {
  renderProofTable();
  renderGraph();
  renderLibrary();
  renderPremiseOptions();
  renderDeductionStack();
  renderTheoremPremiseControls();
  renderTargetStatus();
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function installEvents() {
  el.setTargetBtn.addEventListener("click", setTarget);
  el.targetInput.addEventListener("keydown", (event) => {
    if (event.key === "Enter") setTarget();
  });
  el.addStepBtn.addEventListener("click", addStep);
  el.checkCurrentBtn.addEventListener("click", checkCurrentInput);
  el.enterDeductionBtn.addEventListener("click", enterDeductionLayer);
  el.exitDeductionBtn.addEventListener("click", exitDeductionLayer);
  el.saveTheoremBtn.addEventListener("click", saveCurrentTheorem);
  el.loadDemoBtn.addEventListener("click", loadDemo);
  el.resetProofBtn.addEventListener("click", resetProof);
  el.dependencyGraphBtn.addEventListener("click", renderTheoremDependencyGraph);
  el.clearLibraryBtn.addEventListener("click", clearLibrary);
  el.sourceModes.forEach((item) => item.addEventListener("change", updateModeControls));
  el.premiseSelect.addEventListener("change", () => {
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (premise) el.formulaInput.value = premise.formula;
  });
  el.theoremSelect.addEventListener("change", () => {
    const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value);
    if (theorem) {
      el.formulaInput.disabled = false;
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
      renderTheoremPremiseControls();
    }
  });
}

function boot() {
  axiomSchemas.forEach((axiom) => {
    axiom.ast = parseFormula(axiom.text);
  });
  clearLegacySharedWorkspace();
  loadTheorems();
  installEvents();
  const restored = loadWorkspace();
  if (restored) {
    setMessage("已恢复刷新前的证明过程", "good");
    render();
  } else {
    render();
  }
  updateModeControls();
}

boot();
