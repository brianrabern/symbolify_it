// helloForm.js

const helloForm = () => {
  const [name, setName] = useState("");
  const [greeting, setGreeting] = useState("");

  const handleSubmit = async (e) => {
    e.preventDefault();

    try {
      const response = await fetch("/api/hello", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({ name }),
      });

      if (!response.ok) {
        throw new Error("Failed to fetch the data.");
      }

      const data = await response.text();
      setGreeting(data);
    } catch (error) {
      console.error("Error:", error);
      setGreeting("Error: Unable to process the request");
    }
  };

  return (
    <form onSubmit={handleSubmit}>
      <label>
        Enter your name:
        <input
          type="text"
          value={name}
          onChange={(e) => setName(e.target.value)}
        />
      </label>
      <button type="submit">Submit</button>
      <div>{greeting}</div>
    </form>
  );
};

export default helloForm;
