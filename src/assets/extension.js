(function () {
    const SERVER = 'http://{{addr}}:{{port}}';

    const OUTPUT_UPDATE_INTERVAL_MS = 250;
    const OUTPUT_FAILED_UPDATE_INTERVAL_MS = 1000;
    const OUTPUT_MAX_SIZE = 1024 * 1024;

    function request(info) {
        const req = new XMLHttpRequest();
        req.onreadystatechange = () => {
            if (req.readyState !== XMLHttpRequest.DONE) return;

            if (req.status === 200) {
                (info.onOk || (() => {}))(req.responseText);
            } else {
                (info.onErr || (() => {}))(req.status, req.responseText);
            }
        };
        req.open(info.method, info.url, true);
        req.send(info.body);
    }

    function TerminalMorph(ext) {
        this.init();
        this.ext = ext;
    }
    TerminalMorph.prototype = new DialogBoxMorph();
    TerminalMorph.prototype.constructor = TerminalMorph;
    TerminalMorph.uber = DialogBoxMorph.prototype;
    TerminalMorph.instance = null;

    TerminalMorph.prototype.init = function() {
        TerminalMorph.uber.init.call(this);

        this.labelString = 'Native Terminal';
        this.createLabel();

        this.minWidth = 400;
        this.minHeight = 300;

        this.defaultWidth = 700;
        this.defaultHeight = 500;

        this.titleOffset = 5;
        this.topOffset = 20;
        this.padding = 20;

        this.previousRunning = null;

        this.bounds.setWidth(Math.max(this.defaultWidth, this.minWidth));
        this.bounds.setHeight(Math.max(this.defaultHeight, this.minHeight));

        this.handle = new HandleMorph(this, this.minWidth, this.minHeight, this.corner, this.corner);

        this.add(this.contentFrame = new ScrollFrameMorph());
        this.contentFrame.addContents(this.content = new TextMorph(''));
        this.contentFrame.color = new Color(41, 41, 41);
        this.content.color = new Color(255, 255, 255);

        this.contentFrame.acceptsDrops = false;
        this.contentFrame.contents.acceptsDrops = false;

        this.add(this.leftTools = new AlignmentMorph('row'));
        this.add(this.centerTools = new AlignmentMorph('row'));
        this.add(this.rightTools = new AlignmentMorph('row'));

        function makeSpacer(width) {
            const res = new Morph();
            res.setWidth(width);
            res.setHeight(1);
            res.alpha = 0;
            return res;
        }

        const darkBackgroundColor = new Color(67, 67, 67);
        const darkHighlightColor = new Color(41, 41, 41);
        const darkPressColor = new Color(20, 20, 20);

        // ----------------------------------------------------------------------------------------

        this.leftTools.add(this.uploadButton = new PushButtonMorph(null, () => request({
            method: 'POST',
            url: `${SERVER}/set-project`,
            onErr: alert,
            body: this.ext.ide.getSerializedRole(),
        }), 'Upload'));

        this.leftTools.add(makeSpacer(10));

        this.leftTools.add(this.clearButton = new PushButtonMorph(null, () => this.setText(''), 'Clear'));

        // ----------------------------------------------------------------------------------------

        this.centerTools.add(this.runButton = new PushButtonMorph(null, () => request({
            method: 'POST',
            url: `${SERVER}/send-input`,
            onErr: alert,
            body: 'start',
        }), new SymbolMorph('flag', 12)));
        this.runButton.color = darkBackgroundColor;
        this.runButton.highlightColor = darkHighlightColor;
        this.runButton.pressColor = darkPressColor;
        this.runButton.label.color = new Color(0, 200, 0);
        this.runButton.label.shadowColor = null;

        this.centerTools.add(makeSpacer(10));

        this.centerTools.add(this.togglePausedButton = new PushButtonMorph(null, () => request({
            method: 'POST',
            url: `${SERVER}/toggle-paused`,
            onErr: alert,
        }), '$'));
        this.togglePausedButton.color = darkBackgroundColor;
        this.togglePausedButton.highlightColor = darkHighlightColor;
        this.togglePausedButton.pressColor = darkPressColor;
        this.togglePausedButton.labelColor = new Color(255, 220, 0);
        this.togglePausedButton.labelShadowColor = null;

        this.centerTools.add(makeSpacer(10));

        this.centerTools.add(this.stopButton = new PushButtonMorph(null, () => request({
            method: 'POST',
            url: `${SERVER}/send-input`,
            onErr: alert,
            body: 'stop',
        }), new SymbolMorph('octagon', 12)));
        this.stopButton.color = darkBackgroundColor;
        this.stopButton.highlightColor = darkHighlightColor;
        this.stopButton.pressColor = darkPressColor;
        this.stopButton.label.color = new Color(200, 0, 0);
        this.stopButton.label.shadowColor = null;

        // ----------------------------------------------------------------------------------------

        this.rightTools.add(this.closeButton = new PushButtonMorph(null, () => {
            this.hide();
        }, 'Close'));

        // ----------------------------------------------------------------------------------------

        this.fixLayout();

        const updateLoop = () => {
            request({
                method: 'POST',
                url: `${SERVER}/pull`,
                onOk: res => {
                    const { running, output, errors } = JSON.parse(res);
                    try {
                        if (this.previousRunning !== running) {
                            this.previousRunning = running;
                            this.togglePausedButton.labelString = running ? new SymbolMorph('pause', 12) : new SymbolMorph('pointRight', 12);
                            this.togglePausedButton.createLabel();
                            this.togglePausedButton.fixLayout();
                            this.togglePausedButton.rerender();
                            this.fixLayout();
                        }
                        if (output.length > 0) {
                            const full = this.content.text + output;
                            const clipped = full.substring(full.length - OUTPUT_MAX_SIZE);
                            this.setText(clipped);
                            this.gotoBottom();
                        }
                        if (errors.length > 0) {
                            const ide = this.ext.ide;
                            const lookup = {};
                            const walk = root => {
                                if (root.id) (lookup[root.id] || (lookup[root.id] = [])).push(root);
                                for (const child of root.children) {
                                    walk(child);
                                }
                            };

                            walk(world);
                            for (const block of ide.stage.globalBlocks) {
                                walk(block.body.expression);
                            }
                            for (const entity of [ide.stage, ...ide.sprites.contents]) {
                                for (const block of entity.customBlocks) {
                                    walk(block.body.expression);
                                }
                            }

                            const formatVars = entries => entries.map(entry => `${entry.name} = ${entry.value}`).join('\n');

                            for (const error of errors) {
                                const globals = formatVars(error.globals);
                                const fields = formatVars(error.fields);

                                const commentFamily = [];
                                const errorComment = comment => {
                                    commentFamily.push(comment);

                                    comment.color = new Color(200, 0, 0);
                                    comment.borderColor = new Color(160, 0, 0);
                                    comment.titleBar.color = new Color(160, 0, 0);
                                    comment.titleBar.borderColor = new Color(120, 0, 0);
                                    comment.contents.color = new Color(255, 255, 255);

                                    comment.destroy = () => {
                                        for (const x of commentFamily) {
                                            CommentMorph.prototype.destroy.apply(x);
                                        }
                                    };
                                    comment.fullCopy = () => errorComment(CommentMorph.prototype.fullCopy.apply(comment));

                                    return comment;
                                };
                                for (const entry of error.trace) {
                                    const locals = formatVars(entry.locals);
                                    const blocks = lookup[entry.location];
                                    if (blocks !== undefined) {
                                        for (const block of blocks) {
                                            const vars = [locals, fields, globals].filter(x => x.length).join('\n\n');
                                            let content = error.cause;
                                            if (vars.length) content += `\n\n${vars}`;

                                            const comment = errorComment(new CommentMorph(content));

                                            if (block.comment) block.comment.destroy();

                                            block.comment = comment;
                                            comment.block = block;
                                            comment.align();
                                            block.fixLayout();
                                            block.rerender();
                                        }
                                    } else {
                                        console.warn('failed to find block', entry.location, error);
                                    }
                                }
                            }
                        }
                    } finally {
                        this.updateLoopTimer = setTimeout(updateLoop, OUTPUT_UPDATE_INTERVAL_MS);
                    }
                },
                onErr: (status, res) => {
                    console.error('pull status failed', status, res);
                    this.updateLoopTimer = setTimeout(updateLoop, OUTPUT_FAILED_UPDATE_INTERVAL_MS);
                },
            });
        };
        this.updateLoopTimer = setTimeout(updateLoop, OUTPUT_UPDATE_INTERVAL_MS);
    };

    TerminalMorph.prototype.setText = function (txt) {
        this.content.text = txt;
        this.content.changed();
        this.content.fixLayout();
        this.content.rerender();
        this.fixLayout();
    };
    TerminalMorph.prototype.gotoBottom = function () {
        this.content.setBottom(this.contentFrame.bottom());
    };

    TerminalMorph.prototype.fixLayout = function () {
        if (this.leftTools) {
            this.leftTools.fixLayout();
            this.leftTools.setBottom(this.bottom() - this.padding);
            this.leftTools.setLeft(this.left() + this.padding);
        }

        if (this.centerTools) {
            this.centerTools.fixLayout();
            this.centerTools.setCenter(this.center());
            this.centerTools.setBottom(this.bottom() - this.padding);
        }

        if (this.rightTools) {
            this.rightTools.fixLayout();
            this.rightTools.setBottom(this.bottom() - this.padding);
            this.rightTools.setRight(this.right() - this.padding - this.handle.width());
        }

        if (this.contentFrame) {
            this.contentFrame.setExtent(new Point(
                this.right() - this.left() - 2 * this.padding,
                this.bottom() - this.top() - this.topOffset - 2.5 * this.padding - this.leftTools.height()
            ));
            this.contentFrame.setTop(this.top() + this.topOffset + this.padding);
            this.contentFrame.setLeft(this.left() + this.padding);
        }

        if (this.label) {
            this.label.setCenter(this.center());
            this.label.setTop(this.top() + this.titleOffset);
        }
    };

    class NativeExtension extends Extension {
        constructor(ide) {
            super('Native');
            this.ide = ide;
        }

        onOpenRole() {}

        getMenu() {
            return {
                'Open Terminal': () => {
                    if (!TerminalMorph.instance) TerminalMorph.instance = new TerminalMorph(this);
                    else TerminalMorph.instance.show();

                    TerminalMorph.instance.popUp(world);
                },
            };
        }

        getCategories() {
            return [
                new Extension.Category('native', new Color(160, 20, 20)),
            ];
        }

        getPalette() {
            const blocks = [
                new Extension.Palette.Block('nativeRunSyscall'),
                new Extension.Palette.Block('nativeCallSyscall'),
                new Extension.Palette.Block('nativeSyscallError'),
            ];
            return [
                new Extension.PaletteCategory('native', blocks, SpriteMorph),
                new Extension.PaletteCategory('native', blocks, StageMorph),
            ];
        }

        getBlocks() {
            const fail = () => {
                throw Error("syscalls can't be used in the browser! run on native hardware!");
            };
            return [
                new Extension.Block('nativeRunSyscall', 'command', 'native', 'syscall %syscall %exp', [], fail),
                new Extension.Block('nativeCallSyscall', 'reporter', 'native', 'syscall %syscall %exp', [], fail),
                new Extension.Block('nativeSyscallError', 'reporter', 'native', 'error', [], fail),
            ];
        }

        getLabelParts() {
            return [
                new Extension.LabelPart('syscall', () => new InputSlotMorph(
                    null, // text
                    false, // numeric
                    {{syscalls}},
                    true, // readonly
                )),
            ];
        }
    }

    NetsBloxExtensions.register(NativeExtension);
})();
