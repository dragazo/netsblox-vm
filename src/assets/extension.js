(function () {
    const SERVER = 'http://{{addr}}:{{port}}';

    const OUTPUT_UPDATE_INTERVAL_MS = 250;
    const OUTPUT_FAILED_UPDATE_INTERVAL_MS = 10000;
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

        this.minWidth = 300;
        this.minHeight = 300;

        this.defaultWidth = 700;
        this.defaultHeight = 500;

        this.titleOffset = 5;
        this.topOffset = 20;
        this.padding = 20;

        this.bounds.setWidth(Math.max(this.defaultWidth, this.minWidth));
        this.bounds.setHeight(Math.max(this.defaultHeight, this.minHeight));

        this.handle = new HandleMorph(this, this.minWidth, this.minHeight, this.corner, this.corner);

        this.add(this.contentFrame = new ScrollFrameMorph());
        this.contentFrame.addContents(this.content = new TextMorph(''));
        this.contentFrame.color = new Color(41, 41, 41);
        this.content.color = new Color(255, 255, 255);

        this.add(this.leftTools = new AlignmentMorph('row'));
        this.add(this.rightTools = new AlignmentMorph('row'));

        function makeSpacer(width) {
            const res = new Morph();
            res.setWidth(width);
            res.setHeight(1);
            res.alpha = 0;
            return res;
        }

        this.leftTools.add(this.runButton = new PushButtonMorph(null, async () => {
            request({
                method: 'POST',
                url: `${SERVER}/run`,
                onErr: alert,
                body: this.ext.ide.getSerializedRole(),
            });
        }, 'Run'));

        this.leftTools.add(makeSpacer(10));

        this.leftTools.add(this.stopButton = new PushButtonMorph(null, () => {
            this.setText('');
        }, 'Clear'));

        this.rightTools.add(this.closeButton = new PushButtonMorph(null, () => {
            this.hide();
        }, 'Close'));

        this.fixLayout();

        const updateLoop = () => {
            request({
                method: 'GET',
                url: `${SERVER}/pull`,
                onOk: res => {
                    const { output, errors } = JSON.parse(res);
                    try {
                        if (output.length > 0) {
                            const full = this.content.text + output;
                            const clipped = full.substring(full.length - OUTPUT_MAX_SIZE);
                            this.setText(clipped);
                            this.gotoBottom();
                        }
                        if (errors.length > 0) {
                            const codeRoot = this.ext.ide.room.ide;
                            const lookup = {};
                            const walk = root => {
                                lookup[root.id] = root;
                                for (const child of root.children) {
                                    walk(child);
                                }
                            };

                            for (const entity of [codeRoot.stage, ...codeRoot.sprites.contents]) {
                                for (const script of entity.scripts.children) {
                                    walk(script);
                                }
                            }

                            for (const error of errors) {
                                const block = lookup[error.location];
                                if (block !== undefined) {
                                    const comment = new CommentMorph(error.cause);
                                    comment.color = new Color(200, 0, 0);
                                    comment.borderColor = new Color(160, 0, 0);
                                    comment.titleBar.color = new Color(160, 0, 0);
                                    comment.titleBar.borderColor = new Color(120, 0, 0);
                                    comment.contents.color = new Color(255, 255, 255);

                                    if (block.comment) block.comment.destroy();

                                    block.comment = comment;
                                    comment.block = block;
                                    comment.align();
                                    block.fixLayout();
                                    block.rerender();
                                } else {
                                    console.warn('failed to find block', error);
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
