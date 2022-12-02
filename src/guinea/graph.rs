use egui::DragValue;
use std::{borrow::Cow, collections::HashMap};

use crate::guinea::graph::ConcSymb::Concrete;
use crate::guinea::graph::Sort::{Bitvec, Boolean, Immediate};
use egui_node_graph::*;

// ========= First, define your user data types =============

#[derive(Clone, Debug, Copy, Hash, Eq, PartialEq)]
pub enum ConcSymb {
    Concrete(u64),
    // Symbolic(u64),
}

#[derive(Clone, Debug)]
pub enum Sort {
    Boolean(bool),
    Bitvec(ConcSymb),
    String(String),
    Array(HashMap<ConcSymb, ConcSymb>),
    Immediate(u64),
    Error,
}

impl Default for Sort {
    fn default() -> Self {
        Bitvec(ConcSymb::Concrete(0))
    }
}

impl Sort {
    fn default_bool() -> Self {
        Boolean(false)
    }

    fn default_array() -> Self {
        Self::Array(HashMap::new())
    }

    fn default_string() -> Self {
        Self::String("no name".to_string())
    }

    fn default_imm() -> Self {
        Immediate(0)
    }
}

/// The NodeData holds a custom data struct inside each node. It's useful to
/// store additional information that doesn't live in parameters. For this
/// example, the node data stores the template (i.e. the "type") of the node.
pub struct BeatorNodeData {
    template: BeatorTemplate,
}

/// `DataType`s are what defines the possible range of connections when
/// attaching two ports together. The graph UI will make sure to not allow
/// attaching incompatible datatypes.
#[derive(PartialEq, Eq)]
pub enum BeatorDataType {
    Sort,
}

/// In the graph, input parameters can optionally have a constant value. This
/// value can be directly edited in a widget inside the node itself.
///
/// There will usually be a correspondence between DataTypes and ValueTypes. But
/// this library makes no attempt to check this consistency. For instance, it is
/// up to the user code in this example to make sure no parameter is created
/// with a DataType of Scalar and a ValueType of Vec2.
#[derive(Clone, Debug)]
pub enum BeatorValueType {
    Sort { value: Sort },
}

impl Default for BeatorValueType {
    fn default() -> Self {
        // NOTE: This is just a dummy `Default` implementation. The library
        // requires it to circumvent some internal borrow checker issues.
        Self::Sort {
            value: Sort::Bitvec(ConcSymb::Concrete(0)),
        }
    }
}

impl BeatorValueType {
    pub fn try_to_sort(self) -> anyhow::Result<Sort> {
        let BeatorValueType::Sort { value } = self;
        Ok(value)
    }
}

/// NodeTemplate is a mechanism to define node templates. It's what the graph
/// will display in the "new node" popup. The user code needs to tell the
/// library how to convert a NodeTemplate into a Node.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "persistence", derive(serde::Serialize, serde::Deserialize))]
pub enum BeatorTemplate {
    MemoryConst,
    Const,
    Read,
    Write,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Sll,
    Srl,
    Ult,
    Ext,
    Ite,
    Eq,
    And,
    Not,
    State,
    Next,
    Input,
    Bad,
}

/// The response type is used to encode side-effects produced when drawing a
/// node in the graph. Most side-effects (creating new nodes, deleting existing
/// nodes, handling connections...) are already handled by the library, but this
/// mechanism allows creating additional side effects from user code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeatorResponse {
    SetActiveNode(NodeId),
    ClearActiveNode,
}

/// The graph 'global' state. This state struct is passed around to the node and
/// parameter drawing callbacks. The contents of this struct are entirely up to
/// the user. For this example, we use it to keep track of the 'active' node.
#[derive(Default)]
#[cfg_attr(feature = "persistence", derive(serde::Serialize, serde::Deserialize))]
pub struct BeatorGraphState {
    pub active_node: Option<NodeId>,
}

// =========== Then, you need to implement some traits ============

// A trait for the data types, to tell the library how to display them
impl DataTypeTrait<BeatorGraphState> for BeatorDataType {
    fn data_type_color(&self, _user_state: &mut BeatorGraphState) -> egui::Color32 {
        match self {
            BeatorDataType::Sort => egui::Color32::from_rgb(255, 0, 0),
        }
    }

    fn name(&self) -> Cow<'_, str> {
        match self {
            BeatorDataType::Sort => Cow::Borrowed("Sort"),
        }
    }
}

// A trait for the node kinds, which tells the library how to build new nodes
// from the templates in the node finder
impl NodeTemplateTrait for BeatorTemplate {
    type NodeData = BeatorNodeData;
    type DataType = BeatorDataType;
    type ValueType = BeatorValueType;
    type UserState = BeatorGraphState;

    fn node_finder_label(&self, _user_state: &mut Self::UserState) -> Cow<'_, str> {
        Cow::Borrowed(match self {
            BeatorTemplate::Const => "Const",
            BeatorTemplate::Read => "Read",
            BeatorTemplate::Write => "Write",
            BeatorTemplate::Add => "Addition",
            BeatorTemplate::Sub => "Subtraction",
            BeatorTemplate::Mul => "Multiplication",
            BeatorTemplate::Div => "Division",
            BeatorTemplate::Rem => "Remainder",
            BeatorTemplate::Sll => "Shift Left Logically",
            BeatorTemplate::Srl => "Shift Right Logically",
            BeatorTemplate::Ult => "Less than",
            BeatorTemplate::Ext => "Extend",
            BeatorTemplate::Ite => "If-then-else",
            BeatorTemplate::Eq => "Equality",
            BeatorTemplate::And => "And",
            BeatorTemplate::Not => "Not",
            BeatorTemplate::State => "State",
            BeatorTemplate::Next => "Next",
            BeatorTemplate::Input => "Input",
            BeatorTemplate::Bad => "Bad",
            BeatorTemplate::MemoryConst => "Const (Memory)",
        })
    }

    fn node_graph_label(&self, user_state: &mut Self::UserState) -> String {
        // It's okay to delegate this to node_finder_label if you don't want to
        // show different names in the node finder and the node itself.
        self.node_finder_label(user_state).into()
    }

    fn user_data(&self, _user_state: &mut Self::UserState) -> Self::NodeData {
        BeatorNodeData { template: *self }
    }

    fn build_node(
        &self,
        graph: &mut Graph<Self::NodeData, Self::DataType, Self::ValueType>,
        _user_state: &mut Self::UserState,
        node_id: NodeId,
    ) {
        // The nodes are created empty by default. This function needs to take
        // care of creating the desired inputs and outputs based on the template

        // We define some closures here to avoid boilerplate. Note that this is
        // entirely optional.
        let input_sort = |graph: &mut BeatorGraph, name: &str, val: Sort| {
            graph.add_input_param(
                node_id,
                name.to_string(),
                BeatorDataType::Sort,
                BeatorValueType::Sort { value: val },
                InputParamKind::ConnectionOrConstant,
                true,
            );
        };

        let output_sort = |graph: &mut BeatorGraph, name: &str| {
            graph.add_output_param(node_id, name.to_string(), BeatorDataType::Sort);
        };

        match self {
            BeatorTemplate::Const => {
                graph.add_input_param(
                    node_id,
                    "Immediate".to_string(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output");
            }
            BeatorTemplate::Read => {
                input_sort(graph, "Memory", Sort::default_array());
                input_sort(graph, "Address", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Write => {
                input_sort(graph, "Memory", Sort::default_array());
                input_sort(graph, "Address", Sort::default());
                input_sort(graph, "Value", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Add
            | BeatorTemplate::Sub
            | BeatorTemplate::Mul
            | BeatorTemplate::Div
            | BeatorTemplate::Rem
            | BeatorTemplate::Sll
            | BeatorTemplate::Srl
            | BeatorTemplate::Ult => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Ext => {
                input_sort(graph, "From", Sort::default());
                input_sort(graph, "Value", Sort::default_imm());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Ite => {
                input_sort(graph, "Condition", Sort::default_bool());
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Eq => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::And => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }

            BeatorTemplate::Not => {
                input_sort(graph, "Value", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::State => {
                input_sort(graph, "Initial Value", Sort::default());
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output")
            }
            BeatorTemplate::Next => {
                input_sort(graph, "State", Sort::default());
                input_sort(graph, "Next", Sort::default());
            }
            BeatorTemplate::Input => {
                graph.add_input_param(
                    node_id,
                    "Value".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
            }
            BeatorTemplate::Bad => {
                input_sort(graph, "Condition", Sort::default_bool());
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output");
            }
            BeatorTemplate::MemoryConst => {
                graph.add_input_param(
                    node_id,
                    "Immediate".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_array(),
                    },
                    InputParamKind::ConstantOnly,
                    false,
                );
                output_sort(graph, "Output");
            }
        }
    }
}

pub struct AllBeatorNodeTemplates;

impl NodeTemplateIter for AllBeatorNodeTemplates {
    type Item = BeatorTemplate;

    fn all_kinds(&self) -> Vec<Self::Item> {
        // This function must return a list of node kinds, which the node finder
        // will use to display it to the user. Crates like strum can reduce the
        // boilerplate in enumerating all variants of an enum.
        vec![
            BeatorTemplate::Const,
            BeatorTemplate::MemoryConst,
            BeatorTemplate::Read,
            BeatorTemplate::Write,
            BeatorTemplate::Add,
            BeatorTemplate::Sub,
            BeatorTemplate::Mul,
            BeatorTemplate::Div,
            BeatorTemplate::Rem,
            BeatorTemplate::Sll,
            BeatorTemplate::Srl,
            BeatorTemplate::Ult,
            BeatorTemplate::Ext,
            BeatorTemplate::Ite,
            BeatorTemplate::Eq,
            BeatorTemplate::And,
            BeatorTemplate::Not,
            BeatorTemplate::State,
            BeatorTemplate::Next,
            BeatorTemplate::Input,
            BeatorTemplate::Bad,
        ]
    }
}

impl WidgetValueTrait for BeatorValueType {
    type Response = BeatorResponse;
    type UserState = BeatorGraphState;
    type NodeData = BeatorNodeData;
    fn value_widget(
        &mut self,
        param_name: &str,
        _node_id: NodeId,
        ui: &mut egui::Ui,
        _user_state: &mut BeatorGraphState,
        _node_data: &BeatorNodeData,
    ) -> Vec<BeatorResponse> {
        // This trait is used to tell the library which UI to display for the
        // inline parameter widgets.
        match self {
            BeatorValueType::Sort { value } => match value {
                Boolean(val) => {
                    ui.label(param_name);
                    ui.checkbox(val, "value");
                }
                Bitvec(val) => match val {
                    Concrete(x) => {
                        ui.label(param_name);
                        ui.horizontal(|ui| {
                            ui.label("value");
                            ui.add(DragValue::new(x));
                        });
                    }
                },
                Sort::String(val) => {
                    ui.horizontal(|ui| {
                        ui.label("value");
                        ui.text_edit_singleline(val);
                    });
                }
                Sort::Array(_) => {
                    ui.label("Virtual Memory");
                }
                Immediate(val) => {
                    ui.label(format!("Extend by {val}"));
                }
                Sort::Error => {
                    ui.label("Error Input");
                }
            },
        }
        // This allows you to return your responses from the inline widgets.
        Vec::new()
    }
}

impl UserResponseTrait for BeatorResponse {}

impl NodeDataTrait for BeatorNodeData {
    type Response = BeatorResponse;
    type UserState = BeatorGraphState;
    type DataType = BeatorDataType;
    type ValueType = BeatorValueType;

    // This method will be called when drawing each node. This allows adding
    // extra ui elements inside the nodes. In this case, we create an "active"
    // button which introduces the concept of having an active node in the
    // graph. This is done entirely from user code with no modifications to the
    // node graph library.
    fn bottom_ui(
        &self,
        ui: &mut egui::Ui,
        node_id: NodeId,
        _graph: &Graph<BeatorNodeData, BeatorDataType, BeatorValueType>,
        user_state: &mut Self::UserState,
    ) -> Vec<NodeResponse<BeatorResponse, BeatorNodeData>>
    where
        BeatorResponse: UserResponseTrait,
    {
        // This logic is entirely up to the user. In this case, we check if the
        // current node we're drawing is the active one, by comparing against
        // the value stored in the global user state, and draw different button
        // UIs based on that.

        let mut responses = vec![];
        let is_active = user_state
            .active_node
            .map(|id| id == node_id)
            .unwrap_or(false);

        // Pressing the button will emit a custom user response to either set,
        // or clear the active node. These responses do nothing by themselves,
        // the library only makes the responses available to you after the graph
        // has been drawn. See below at the update method for an example.
        if !is_active {
            if ui.button("👁 Set active").clicked() {
                responses.push(NodeResponse::User(BeatorResponse::SetActiveNode(node_id)));
            }
        } else {
            let button =
                egui::Button::new(egui::RichText::new("👁 Active").color(egui::Color32::BLACK))
                    .fill(egui::Color32::GOLD);
            if ui.add(button).clicked() {
                responses.push(NodeResponse::User(BeatorResponse::ClearActiveNode));
            }
        }

        responses
    }
}

type BeatorGraph = Graph<BeatorNodeData, BeatorDataType, BeatorValueType>;
type BeatorEditorState = GraphEditorState<
    BeatorNodeData,
    BeatorDataType,
    BeatorValueType,
    BeatorTemplate,
    BeatorGraphState,
>;

#[derive(Default)]
pub struct NodeGraph {
    // The `GraphEditorState` is the top-level object. You "register" all your
    // custom types by specifying it as its generic parameters.
    pub state: BeatorEditorState,

    pub user_state: BeatorGraphState,
    pub out: String,
}

type OutputsCache = HashMap<OutputId, BeatorValueType>;

/// Recursively evaluates all dependencies of this node, then evaluates the node itself.
pub fn evaluate_node(
    graph: &BeatorGraph,
    node_id: NodeId,
    outputs_cache: &mut OutputsCache,
) -> anyhow::Result<BeatorValueType> {
    // To solve a similar problem as creating node types above, we define an
    // Evaluator as a convenience. It may be overkill for this small example,
    // but something like this makes the code much more readable when the
    // number of nodes starts growing.

    struct Evaluator<'a> {
        graph: &'a BeatorGraph,
        outputs_cache: &'a mut OutputsCache,
        node_id: NodeId,
    }
    impl<'a> Evaluator<'a> {
        fn new(
            graph: &'a BeatorGraph,
            outputs_cache: &'a mut OutputsCache,
            node_id: NodeId,
        ) -> Self {
            Self {
                graph,
                outputs_cache,
                node_id,
            }
        }
        fn evaluate_input(&mut self, name: &str) -> anyhow::Result<BeatorValueType> {
            // Calling `evaluate_input` recursively evaluates other nodes in the
            // graph until the input value for a paramater has been computed.
            evaluate_input(self.graph, self.node_id, name, self.outputs_cache)
        }
        fn populate_output(
            &mut self,
            name: &str,
            value: BeatorValueType,
        ) -> anyhow::Result<BeatorValueType> {
            // After computing an output, we don't just return it, but we also
            // populate the outputs cache with it. This ensures the evaluation
            // only ever computes an output once.
            //
            // The return value of the function is the "final" output of the
            // node, the thing we want to get from the evaluation. The example
            // would be slightly more contrived when we had multiple output
            // values, as we would need to choose which of the outputs is the
            // one we want to return. Other outputs could be used as
            // intermediate values.
            //
            // Note that this is just one possible semantic interpretation of
            // the graphs, you can come up with your own evaluation semantics!
            populate_output(self.graph, self.outputs_cache, self.node_id, name, value)
        }
        fn input_sort(&mut self, name: &str) -> anyhow::Result<Sort> {
            self.evaluate_input(name)?.try_to_sort()
        }
        fn output_sort(&mut self, name: &str, value: Sort) -> anyhow::Result<BeatorValueType> {
            self.populate_output(name, BeatorValueType::Sort { value })
        }
    }

    let node = &graph[node_id];
    let mut evaluator = Evaluator::new(graph, outputs_cache, node_id);
    match node.user_data.template {
        BeatorTemplate::Const => {
            let value = evaluator.input_sort("Immediate")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Read => {
            let memory = evaluator.input_sort("Memory")?;
            let address = evaluator.input_sort("Address")?;

            match (memory, address) {
                (Sort::Array(mem), Bitvec(add)) => {
                    evaluator.output_sort("Output", Bitvec(*mem.get(&add).unwrap_or(&Concrete(0))))
                }
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Write => {
            let memory = evaluator.input_sort("Memory")?;
            let address = evaluator.input_sort("Address")?;
            let value = evaluator.input_sort("Value")?;

            match (memory, address, value) {
                (Sort::Array(mut mem), Bitvec(add), Bitvec(val)) => {
                    mem.insert(add, val);
                    evaluator.output_sort("Output", Sort::Array(mem))
                }
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Add => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l + r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Sub => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l - r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Mul => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l * r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Div => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l / r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Rem => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l % r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Sll => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l << r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Srl => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l >> r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ult => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => evaluator.output_sort("Output", Boolean(l < r)),
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ext => {
            let input = evaluator.input_sort("From")?;
            let value = evaluator.input_sort("Value")?;
            match (input, value) {
                (Bitvec(i), Immediate(_)) => evaluator.output_sort("Output", Bitvec(i)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ite => {
            let cond = evaluator.input_sort("Condition")?;
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;

            if let Boolean(cond) = cond {
                evaluator.output_sort("Output", if cond { left } else { right })
            } else {
                Ok(BeatorValueType::Sort { value: Sort::Error })
            }
        }
        BeatorTemplate::Eq => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;

            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => evaluator.output_sort("Output", Boolean(l == r)),
                },
                (Boolean(l), Boolean(r)) => evaluator.output_sort("Output", Boolean(l == r)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::And => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l & r)))
                    }
                },
                (Boolean(l), Boolean(r)) => evaluator.output_sort("Output", Boolean(l && r)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Not => {
            let value = evaluator.input_sort("Value")?;
            match value {
                Boolean(val) => evaluator.output_sort("Output", Boolean(!val)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::State => {
            let value = evaluator.input_sort("Initial Value")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Next => {
            let value = evaluator.input_sort("Next")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Input => {
            let value = evaluator.input_sort("Value")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Bad => {
            let value = evaluator.input_sort("Condition")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::MemoryConst => {
            let value = evaluator.input_sort("Immediate")?;
            evaluator.output_sort("Output", value)
        }
    }
}

fn populate_output(
    graph: &BeatorGraph,
    outputs_cache: &mut OutputsCache,
    node_id: NodeId,
    param_name: &str,
    value: BeatorValueType,
) -> anyhow::Result<BeatorValueType> {
    let output_id = graph[node_id].get_output(param_name)?;
    outputs_cache.insert(output_id, value.clone());
    Ok(value)
}

// Evaluates the input value of
fn evaluate_input(
    graph: &BeatorGraph,
    node_id: NodeId,
    param_name: &str,
    outputs_cache: &mut OutputsCache,
) -> anyhow::Result<BeatorValueType> {
    let input_id = graph[node_id].get_input(param_name)?;

    // The output of another node is connected.
    if let Some(other_output_id) = graph.connection(input_id) {
        // The value was already computed due to the evaluation of some other
        // node. We simply return value from the cache.
        if let Some(other_value) = outputs_cache.get(&other_output_id) {
            Ok(other_value.clone())
        }
        // This is the first time encountering this node, so we need to
        // recursively evaluate it.
        else {
            // Calling this will populate the cache
            evaluate_node(graph, graph[other_output_id].node, outputs_cache)?;

            // Now that we know the value is cached, return it
            let val = outputs_cache
                .get(&other_output_id)
                .expect("Cache should be populated")
                .clone();
            Ok(val)
        }
    }
    // No existing connection, take the inline value instead.
    else {
        Ok(graph[input_id].value.clone())
    }
}
