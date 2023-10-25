FROM pytorch/pytorch

RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y git htop atop graphviz && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN pip install --upgrade pip

WORKDIR /workspace

COPY requirements.txt .

RUN pip install -r requirements.txt

EXPOSE 8888

CMD ["jupyter", "notebook", "--ip='0.0.0.0'", "--port=8888", "--no-browser", "--allow-root", "--NotebookApp.token=''", "--notebook-dir=/workspace"]
